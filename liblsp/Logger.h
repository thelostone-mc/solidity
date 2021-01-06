#pragma once

#include <liblsp/protocol.h>
#include <string>

namespace lsp {

/// Logging facility within the scope of a Language Server.
///
/// Since language servers are typically automatically spawned by their clients,
/// logging cannot just go to stderr.
///
/// This API allows proper abstracting logging into the client's log channel.
class Logger
{
public:
	virtual ~Logger() = default;

	virtual void log(protocol::MessageType _type, std::string const& _message) = 0;

	// Convenience helper methods for logging in various severities.
	//
	void logError(std::string const& _msg) { log(protocol::MessageType::Error, _msg); }
	void logWarning(std::string const& _msg) { log(protocol::MessageType::Warning, _msg); }
	void logInfo(std::string const& _msg) { log(protocol::MessageType::Info, _msg); }
	void logMessage(std::string const& _msg) { log(protocol::MessageType::Log, _msg); }
};

} // end namespace
