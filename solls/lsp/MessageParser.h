#include <json/json.h>

#include <iosfwd>
#include <string>
#include <variant>

namespace lsp {

enum class ErrorCode
{
	TransportProtocolError = 1,
	JsonParseError,
	// TODO: more to follow
};

/// Synchronously parses a single JSON-RPC message from input stream.
std::variant<std::string, ErrorCode> parseMessage(std::istream& _inputStream);

} // namespace lsp
