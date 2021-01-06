#include <liblsp/Transport.h>
#include <liblsp/MessageParser.h>

#include <libsolutil/Visitor.h>

#include <boost/algorithm/string.hpp>

#include <istream>
#include <ostream>

using namespace std;

namespace lsp {

JSONTransport::JSONTransport(istream& _in, ostream& _out):
	m_input{ _in },
	m_output{ _out }
{
}

optional<Json::Value> JSONTransport::receive()
{
	auto const headers = parseHeaders();
	if (!headers)
		return nullopt;

	if (!headers->count("content-length"))
		return nullopt;

	string const data = readBytes(stoi(headers->at("content-length")));

	Json::Value jsonMessage;
	string errs;
	solidity::util::jsonParseStrict(data, jsonMessage, &errs);
	if (!errs.empty())
		return nullopt; // JsonParseError

	return {jsonMessage};
}

void JSONTransport::notify(string const& _method, Json::Value const& _message)
{
	Json::Value json;
	json["jsonrpc"] = "2.0";
	json["method"] = _method;
	json["params"] = _message;
	send(json);
}

void JSONTransport::reply(MessageId const& _id, Json::Value const& _message)
{
	Json::Value json;
	json["jsonrpc"] = "2.0";
	json["result"] = _message;
	visit(solidity::util::GenericVisitor{
		[&](int _id) { json["id"] = _id; },
		[&](string const& _id) { json["id"] = _id; },
		[&](monostate) {}
	}, _id);
	send(json);
}

void JSONTransport::error(MessageId const& _id, protocol::ErrorCode _code, string const& _message)
{
	Json::Value json;
	json["jsonrpc"] = "2.0";
	visit(solidity::util::GenericVisitor{
		[&](int _id) { json["id"] = _id; },
		[&](string const& _id) { json["id"] = _id; },
		[&](monostate) {}
	}, _id);
	json["error"]["code"] = static_cast<int>(_code);
	json["error"]["message"] = _message;
	send(json);
}

void JSONTransport::send(Json::Value const& _json)
{
	string const jsonString = solidity::util::jsonCompactPrint(_json);

	m_output << "Content-Length: " << jsonString.size() << "\r\n";
	m_output << "\r\n";
	m_output << jsonString;

	m_output.flush();
}

string JSONTransport::readLine()
{
	string line;

	getline(m_input, line);
	if (!line.empty() && line.back() == '\r')
		line.resize(line.size() - 1);

	return line;
}

optional<JSONTransport::HeaderMap> JSONTransport::parseHeaders()
{
	unordered_map<string, string> headers;

	for (string line = readLine(); !line.empty(); line = readLine())
	{
		auto const delimiterPos = line.find(':');
		if (delimiterPos == string::npos)
			return nullopt;

		auto const name = boost::to_lower_copy(line.substr(0, delimiterPos));
		auto const value = boost::trim_copy(line.substr(delimiterPos + 1));

		headers[name] = value;
	}
	return {headers};
}

string JSONTransport::readBytes(int _n)
{
	if (_n < 0)
		return {};

	string data;
	data.resize(static_cast<string::size_type>(_n));
	m_input.read(data.data(), _n);
	return data;
}

} // end namespace
