#include <solls/LanguageServer.h>
#include <liblsp/Transport.h>
#include <fstream>

#include <sys/types.h> // TODO: nah, that's only for now. make platform independant before merge.
#include <unistd.h>

#include <iostream>

using namespace std::string_literals;

using std::cin;
using std::cout;
using std::exception;
using std::fstream;
using std::string;
using std::string_view;
using std::to_string;

struct DebugLogger { // created for having a second logging channel into a file (for better debugging)
	string m_filename;
	fstream m_stream;

	DebugLogger() = default;
	DebugLogger(DebugLogger&&) = default;
	DebugLogger& operator=(DebugLogger&&) = default;

	DebugLogger(string_view _path):
		m_filename(_path),
		m_stream(m_filename.c_str(), std::ios::trunc | std::ios::out)
	{
	}

	void operator()(string_view _msg)
	{
		if (!m_stream.good())
			return;

		m_stream << _msg << '\n';
	}
};

int main([[maybe_unused]] int argc, [[maybe_unused]] char* argv[])
{
	/* TODO: CLI parameters

		solls [flags ...]
			--evm-version="STRING"
			--allow-paths="STRING_LIST,..."
			--mode=MODE                      with MODE being one of: solidity, linker, assembly, yul, strict-assembly
			--transport=stdio                Do the transport via STDIO.
			--transport=tcp://BIND:PORT      Do the transport via TCP/IP (for debugging the server only).
			--log-trace=PATH                 Path to local filename to log I/O trace messages to.

		The project root is the one specified via LSP-Hello handshake,
		and all sol files in there may be whitelisted.

		TODO: the TcpTransport should maybe use Boost.Asio so we get a tcp_stream on all platforms?
	*/

	auto const logPath = "/tmp/solls."s + to_string(getpid());
	auto debugLogger = DebugLogger(logPath);

	try
	{
		auto transport = lsp::JSONTransport{cin, cout, [&](auto msg) { debugLogger(msg); }};
		auto languageServer = solidity::LanguageServer{transport, [&](auto msg) { debugLogger(msg); }};
		return languageServer.run();
	}
	catch (exception const& e)
	{
		debugLogger("Unhandled exception caught."s + e.what());
	}
}
