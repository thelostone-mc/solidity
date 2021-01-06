#include <liblsp/OutputGenerator.h>
#include <libsolutil/Visitor.h>
#include <variant>

namespace lsp {

using namespace std;

OutputGenerator::NotificationInfo OutputGenerator::operator()(protocol::Notification const& _message)
{
	return visit(*this, _message);
}

OutputGenerator::NotificationInfo OutputGenerator::operator()(protocol::CancelRequest const& _message)
{
	Json::Value params;

	visit(
		solidity::util::GenericVisitor{
			[&](int _id) {
				params["id"] = _id;
			},
			[&](string const& _id) {
				params["id"] = _id;
			}
		},
		_message.id
	);

	return {"$/cancelRequest", params};
}

Json::Value OutputGenerator::toJson(Range const& _range)
{
	Json::Value json;
	json["start"]["line"] = _range.start.line;
	json["start"]["character"] = _range.start.column;
	json["end"]["line"] = _range.end.line;
	json["end"]["character"] = _range.end.column;
	return json;
}

OutputGenerator::NotificationInfo OutputGenerator::operator()(protocol::PublishDiagnosticsParams const& _params)
{
	Json::Value params;

	params["uri"] = _params.uri;

	if (_params.version)
		params["version"] = _params.version.value();

	params["diagnostics"] = Json::arrayValue;
	for (protocol::Diagnostic const& diag: _params.diagnostics)
	{
		Json::Value jsonDiag;

		jsonDiag["range"] = toJson(diag.range);

		if (diag.severity.has_value())
			jsonDiag["severity"] = static_cast<int>(diag.severity.value());

		visit(
			solidity::util::GenericVisitor{
				[&](int _code) { jsonDiag["code"] = _code; },
				[&](string const& _code) { jsonDiag["code"] = _code; },
				[&](monostate) { }
			},
			diag.code
		);

		if (diag.source.has_value())
			jsonDiag["source"] = diag.source.value();

		jsonDiag["message"] = diag.message;

		if (!diag.diagnosticTag.empty())
			for (protocol::DiagnosticTag tag: diag.diagnosticTag)
				jsonDiag["diagnosticTag"].append(static_cast<int>(tag));

		if (!diag.relatedInformation.empty())
		{
			for (protocol::DiagnosticRelatedInformation const& related: diag.relatedInformation)
			{
				Json::Value json;
				json["message"] = related.message;
				json["location"]["uri"] = related.location.uri;
				json["location"]["range"] = toJson(related.location.range);
				jsonDiag["relatedInformation"].append(json);
			}
		}

		params["diagnostics"].append(jsonDiag);
	}

	return {"textDocument/publishDiagnostics", params};
}

OutputGenerator::NotificationInfo OutputGenerator::operator()(protocol::LogMessageParams const& _params)
{
	Json::Value params = Json::objectValue;
	params["type"] = static_cast<int>(_params.type);
	params["message"] = _params.message;

	return {"window/logMessage", params};
}

Json::Value OutputGenerator::operator()(protocol::Response const& _response)
{
	return visit(*this, _response);
}

Json::Value OutputGenerator::operator()(protocol::InitializeResult const& _response)
{
	Json::Value reply;

	if (_response.serverInfo.has_value())
	{
		reply["serverInfo"]["name"] = _response.serverInfo->name;
		if (_response.serverInfo->version.has_value())
			reply["serverInfo"]["version"] = _response.serverInfo->version.value();
	}

	if (_response.capabilities.hoverProvider)
		reply["hoverProvider"] = true;

	reply["capabilities"]["hoverProvider"] = _response.capabilities.hoverProvider;
	reply["capabilities"]["textDocumentSync"]["openClose"] = _response.capabilities.textDocumentSync.openClose;
	reply["capabilities"]["textDocumentSync"]["change"] = static_cast<int>(_response.capabilities.textDocumentSync.change);
	reply["capabilities"]["definitionProvider"] = static_cast<int>(_response.capabilities.definitionProvider);

	return reply;
}

OutputGenerator::MethodInfo OutputGenerator::operator()(protocol::RegistrationParams const& _params)
{
	Json::Value regs = Json::arrayValue;
	for (protocol::Registration const& registration: _params.registrations)
	{
		Json::Value reg;
		reg["id"] = registration.id;
		reg["method"] = registration.method;
		regs.append(reg);
	}

	Json::Value method;
	method["registrations"] = regs;
	return {"client/registerCapability", method};
}

Json::Value OutputGenerator::operator()(protocol::DefinitionReplyParams const& _params)
{
	Json::Value json = Json::objectValue;

	json["range"]["start"]["line"] = _params.range.start.line;
	json["range"]["start"]["character"] = _params.range.start.column;
	json["range"]["end"]["line"] = _params.range.end.line;
	json["range"]["end"]["character"] = _params.range.end.column;
	json["uri"] = _params.uri;

	return json;
}

} // end namespace
