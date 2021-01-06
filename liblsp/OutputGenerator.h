#pragma once

#include <libsolutil/JSON.h>
#include <liblsp/protocol.h>

#include <tuple>

namespace lsp {

struct OutputGenerator
{
	// notifications
	struct NotificationInfo { std::string method; Json::Value params; };
	NotificationInfo operator()(protocol::CancelRequest const&);
	NotificationInfo operator()(protocol::Notification const&);
	NotificationInfo operator()(protocol::PublishDiagnosticsParams const&);
	NotificationInfo operator()(protocol::LogMessageParams const&);

	// replies
	Json::Value operator()(protocol::DefinitionReplyParams const&);
	Json::Value operator()(protocol::InitializeResult const&);
	Json::Value operator()(protocol::Response const&);

	// methods from server-to-client
	struct MethodInfo { std::string method; Json::Value params; };
	MethodInfo operator()(protocol::RegistrationParams const&);

	Json::Value toJson(Range const& _range);

	// TODO: Obviousely, here's more to come...
};

} // end namespace
