#include <liblsp/InputHandler.h>
#include <liblsp/Logger.h>
#include <libsolutil/JSON.h>

#include <array>

using namespace lsp::protocol;

using namespace std;
using namespace std::placeholders;

namespace lsp {

InputHandler::InputHandler(Logger& _logger):
	m_logger{ _logger },
	m_handlers{
		{"cancelRequest", bind(&InputHandler::cancelRequest, this, _1, _2)},
		{"initialize", bind(&InputHandler::initializeRequest, this, _1, _2)},
		{"initialized", bind(&InputHandler::initialized, this, _1, _2)},
		{"textDocument/didOpen", bind(&InputHandler::textDocument_didOpen, this, _1, _2)},
		{"textDocument/didChange", bind(&InputHandler::textDocument_didChange, this, _1, _2)},
		{"textDocument/didClose", bind(&InputHandler::textDocument_didClose, this, _1, _2)},
		{"textDocument/definition", bind(&InputHandler::textDocument_definition, this, _1, _2)},
	}
{
}

optional<Request> InputHandler::handleRequest(Json::Value const& _jsonMessage)
{
	string const methodName = _jsonMessage["method"].asString();

	MessageId const id = _jsonMessage["id"].isInt()
		? MessageId{_jsonMessage["id"].asInt()}
		: _jsonMessage["id"].isString()
			? MessageId{_jsonMessage["id"].asString()}
			: MessageId{};

	if (m_shutdownRequested && methodName != "exit")
	{
		// "If a server receives requests after a shutdown request those requests should error with InvalidRequest"
		// TODO: return InvalidRequest{}
		// TODO: then the handler responds with ErrorCodes::InvalidRequest
		m_logger.logError("Attempting to execute " + methodName + " after shutdown has been requested.");
		return InvalidRequest{id, methodName};
	}

	Json::Value const& jsonArgs = _jsonMessage["params"];

	if (auto const handlerIter = m_handlers.find(methodName); handlerIter != m_handlers.end())
		return handlerIter->second(id, jsonArgs);
	else
		m_logger.logError("InputHandler: Unsupported method: \"" + methodName +"\"");

	return nullopt;
}

optional<CancelRequest> InputHandler::cancelRequest(MessageId const&, Json::Value const& _message)
{
	if (Json::Value id = _message["id"]; id.isInt())
		return CancelRequest{id.asInt()};
	else if (id.isString())
		return CancelRequest{id.asString()};
	else
		return nullopt;
}

optional<ShutdownParams> InputHandler::shutdown(MessageId const&, Json::Value const&)
{
	m_shutdownRequested = true;
	return ShutdownParams{};
}

optional<ExitParams> InputHandler::exit(MessageId const&, Json::Value const&)
{
	return ExitParams{};
}

optional<InitializeRequest> InputHandler::initializeRequest(MessageId const& _id, Json::Value const& _args)
{
	lsp::protocol::InitializeRequest request{};
	request.requestId = _id;

	if (Json::Value pid = _args["processId"]; pid)
		request.processId = pid.asInt();

	if (Json::Value rootPath = _args["rootPath"]; rootPath)
		request.rootPath = rootPath.asString();

	if (Json::Value uri = _args["rootUri"]; uri)
		request.rootUri = uri.asString();

	if (Json::Value trace = _args["trace"]; trace)
	{
		string const name = trace.asString();
		if (name == "messages")
			request.trace = lsp::protocol::Trace::Messages;
		else if (name == "verbose")
			request.trace = lsp::protocol::Trace::Verbose;
		else if (name == "off")
			request.trace = lsp::protocol::Trace::Off;
	}

	if (Json::Value folders = _args["workspaceFolders"]; folders)
	{
		for (Json::Value folder: folders)
		{
			lsp::protocol::WorkspaceFolder wsFolder{};
			wsFolder.name = folder["name"].asString();
			wsFolder.uri = folder["uri"].asString();
			request.workspaceFolders.emplace_back(move(wsFolder));
		}
	}

	// TODO: initializationOptions
	// TODO: ClientCapabilities

	return request;
}

optional<protocol::InitializedNotification> InputHandler::initialized(MessageId const&, Json::Value const&)
{
	// TODO: error checking?
	return InitializedNotification{};
}

optional<DidOpenTextDocumentParams> InputHandler::textDocument_didOpen(MessageId const& _id, Json::Value const& _args)
{
	if (!_args["textDocument"])
		return nullopt;

	DidOpenTextDocumentParams args{};
	args.requestId = _id;
	args.textDocument.uri = _args["textDocument"]["uri"].asString();
	args.textDocument.languageId = _args["textDocument"]["languageId"].asString();
	args.textDocument.version = _args["textDocument"]["version"].asInt();
	args.textDocument.text = _args["textDocument"]["text"].asString();

	return args;
}

optional<protocol::DidChangeTextDocumentParams> InputHandler::textDocument_didChange(MessageId const& _id, Json::Value const& _json)
{
	DidChangeTextDocumentParams didChange{};
	didChange.requestId = _id;
	didChange.textDocument.version = _json["textDocument"]["version"].asInt();
	didChange.textDocument.uri = _json["textDocument"]["uri"].asString();

	for (Json::Value jsonContentChange: _json["contentChanges"])
	{
		if (jsonContentChange.isObject() && jsonContentChange["range"])
		{
			TextDocumentRangedContentChangeEvent rangedChange;
			rangedChange.text = jsonContentChange["text"].asString();

			Json::Value jsonRange = jsonContentChange["range"];

			rangedChange.range.start.line = jsonRange["start"]["line"].asInt();
			rangedChange.range.start.column = jsonRange["start"]["character"].asInt();
			rangedChange.range.end.line = jsonRange["end"]["line"].asInt();
			rangedChange.range.end.column = jsonRange["end"]["character"].asInt();
			didChange.contentChanges.emplace_back(move(rangedChange));
		}
		else
		{
			// TODO: TextDocumentFullContentChangeEvent fullChange;
			m_logger.logInfo("InputHandler: TODO! TextDocumentFullContentChangeEvent!");
		}
	}

	return didChange;
}

optional<protocol::DidCloseTextDocumentParams> InputHandler::textDocument_didClose(MessageId const& _id, Json::Value const& _json)
{
	protocol::DidCloseTextDocumentParams didClose;
	didClose.requestId = _id;
	didClose.textDocument.uri = _json["textDocument"]["uri"].asString();
	return didClose;
}

std::optional<protocol::DefinitionParams> InputHandler::textDocument_definition(MessageId const& _id, Json::Value const& _json)
{
	protocol::DefinitionParams params;
	params.requestId = _id;
	params.textDocument.uri = _json["textDocument"]["uri"].asString();
	params.position.line = _json["position"]["line"].asInt();
	params.position.column = _json["position"]["character"].asInt();
	return params;
}

} // end namespace
