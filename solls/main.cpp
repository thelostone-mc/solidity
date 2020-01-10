#include <solls/LanguageServer.h>
#include <lsp/Transport.h>

using namespace std;

int main([[maybe_unused]] int argc, [[maybe_unused]] char* argv[])
{
	auto transport = lsp::JSONTransport{cin, cout};
	auto languageServer = solidity::LanguageServer{transport};

	return languageServer.run();
}
