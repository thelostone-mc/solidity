#pragma once

#include <liblsp/protocol.h>

#include <libsolutil/JSON.h>

#include <functional>
#include <ostream>
#include <string>
#include <unordered_map>

namespace lsp {

class Logger;

// Handles pure JSON input values by transforming them into LSP objects
class InputHandler
{
public:
	explicit InputHandler(Logger& _logger);

	/// Transforms JSON RPC request message into a higher level LSP request message.
	/// It will return std::nullopt in case of protocol errors.
	std::optional<protocol::Request> handleRequest(Json::Value const& _message);

	// <->
	std::optional<protocol::CancelRequest> cancelRequest(MessageId const&, Json::Value const&);

	// client to server
	std::optional<protocol::InitializeRequest> initializeRequest(MessageId const&, Json::Value const&);
	std::optional<protocol::InitializedNotification> initialized(MessageId const&, Json::Value const&);
	std::optional<protocol::ShutdownParams> shutdown(MessageId const&, Json::Value const&);
	std::optional<protocol::ExitParams> exit(MessageId const&, Json::Value const&);
	std::optional<protocol::DidOpenTextDocumentParams> textDocument_didOpen(MessageId const&, Json::Value const&);
	std::optional<protocol::DidChangeTextDocumentParams> textDocument_didChange(MessageId const&, Json::Value const&);
	std::optional<protocol::DidCloseTextDocumentParams> textDocument_didClose(MessageId const&, Json::Value const&);
	std::optional<protocol::DefinitionParams> textDocument_definition(MessageId const&, Json::Value const&);

private:
	using Handler = std::function<std::optional<protocol::Request>(MessageId const&, Json::Value const&)>;
	using HandlerMap = std::unordered_map<std::string, Handler>;

	Logger& m_logger;
	HandlerMap m_handlers;
	bool m_shutdownRequested = false;
};

}
