#include <lsp/MessageParser.h>
#include <json/json.h>
#include <libsolutil/JSON.h>

#include <boost/algorithm/string.hpp>

#include <istream>
#include <ostream>
#include <string>
#include <unordered_map>
#include <variant>

using namespace std;

namespace lsp {

variant<std::string, ErrorCode> parseMessage(istream& _input)
{
	// Parses a single text line ending with CRLF (or just LF).
	auto const readLine = [&]() -> string {
		string line;
		getline(_input, line);
		if (!line.empty() && line.back() == '\r')
			line.resize(line.size() - 1);
		return line;
	};

	// Reads given number of bytes from input stream.
	auto const readBytes = [&](size_t _n) {
		string data;
		data.resize(_n);
		_input.read(data.data(), streamsize(_n));
		return data;
	};

	using HeaderMap = unordered_map<string, string>;

	// Parses header section including message-delimiting empty line.
	auto const parseHeaders = [&]() -> variant<HeaderMap, ErrorCode> {
		unordered_map<string, string> headers;
		for (string line = readLine(); !line.empty(); line = readLine())
		{
			auto const delimiterPos = line.find(':');
			if (delimiterPos == string::npos)
				return {ErrorCode::TransportProtocolError};

			auto const name = boost::to_lower_copy(line.substr(0, delimiterPos));
			auto const value = boost::trim_copy(line.substr(delimiterPos + 1));
			headers[name] = value;
		}
		return {headers};
	};

	auto const headers = parseHeaders();
	if (holds_alternative<ErrorCode>(headers))
		return get<ErrorCode>(headers);

	if (!get<HeaderMap>(headers).count("content-length"))
		return {ErrorCode::TransportProtocolError};

	size_t const contentLength = static_cast<size_t>(max(0, stoi(get<HeaderMap>(headers).at("content-length"))));
	string const data = readBytes(contentLength);

	return {data};
}

} // namespace lsp

