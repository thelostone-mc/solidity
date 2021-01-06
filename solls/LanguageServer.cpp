#include <solls/LanguageServer.h>

#include <lsp/OutputGenerator.h>
#include <lsp/protocol.h>

#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/ASTVisitor.h>

#include <liblangutil/SourceReferenceExtractor.h>

#include <libsolutil/Visitor.h>
#include <libsolutil/JSON.h>

#include <ostream>

#include <iostream>
#include <string>

using namespace std;
using namespace std::placeholders;

using namespace solidity::langutil;
using namespace solidity::frontend;

namespace solidity {

LanguageServer::LanguageServer(lsp::Transport& _client):
	lsp::Server(_client),
	m_vfs()
{
}

void LanguageServer::operator()(lsp::protocol::CancelRequest const& _args)
{
	auto const id = visit(util::GenericVisitor{
		[](string const& _id) -> string { return _id; },
		[](int _id) -> string { return to_string(_id); }
	}, _args.id);

	logInfo("LanguageServer: Request " + id + " cancelled.");
}

void LanguageServer::operator()(lsp::protocol::ShutdownParams const&)
{
	logInfo("LanguageServer: shutdown requested");
}

void LanguageServer::operator()(lsp::protocol::InitializeRequest const& _args)
{
#if !defined(NDEBUG)
	ostringstream msg;
	msg << "LanguageServer: Initializing, PID :" << _args.processId.value_or(-1) << endl;
	msg << "                rootUri           : " << _args.rootUri.value_or("NULL") << endl;
	msg << "                rootPath          : " << _args.rootPath.value_or("NULL") << endl;
	for (auto const& workspace: _args.workspaceFolders)
		msg << "                workspace folder: " << workspace.name << "; " << workspace.uri << endl;
	logMessage(msg.str());
#endif

	lsp::protocol::InitializeResult result;
	result.requestId = _args.requestId;
	result.capabilities.hoverProvider = true;
	result.capabilities.textDocumentSync.openClose = true;
	result.capabilities.textDocumentSync.change = lsp::protocol::TextDocumentSyncKind::Incremental;
	result.capabilities.definitionProvider = true; // go-to-definition feature

	reply(_args.requestId, result);
}

void LanguageServer::operator()(lsp::protocol::InitializedNotification const&)
{
	// NB: this means the client has finished initializing. Now we could maybe start sending
	// events to the client.
	logMessage("LanguageServer: Client initialized");
}

void LanguageServer::operator()(lsp::protocol::DidOpenTextDocumentParams const& _args)
{
	logMessage("LanguageServer: Opening document: " + _args.textDocument.uri);

	lsp::vfs::File const& file = m_vfs.insert(
		_args.textDocument.uri,
		_args.textDocument.languageId,
		_args.textDocument.version,
		_args.textDocument.text
	);

	validate(file);
}

void LanguageServer::operator()(lsp::protocol::DidChangeTextDocumentParams const& _didChange)
{
	if (lsp::vfs::File* file = m_vfs.find(_didChange.textDocument.uri); file != nullptr)
	{
		if (_didChange.textDocument.version.has_value())
			file->setVersion(_didChange.textDocument.version.value());

		for (lsp::protocol::TextDocumentContentChangeEvent const& contentChange: _didChange.contentChanges)
		{
			visit(util::GenericVisitor{
				[&](lsp::protocol::TextDocumentRangedContentChangeEvent const& change) {
#if !defined(NDEBUG)
					ostringstream str;
					str << "did change: " << change.range << " for '" << change.text << "'";
					logMessage(str.str());
#endif
					file->modify(change.range, change.text);
				},
				[&](lsp::protocol::TextDocumentFullContentChangeEvent const& change) {
					file->replace(change.text);
				}
			}, contentChange);
		}

		validate(*file);
	}
	else
		logError("LanguageServer: File to be modified not opened \"" + _didChange.textDocument.uri + "\"");
}

void LanguageServer::operator()(lsp::protocol::DidCloseTextDocumentParams const& _didClose)
{
	logMessage("LanguageServer: didClose: " + _didClose.textDocument.uri);
}

void LanguageServer::validateAll()
{
	for (reference_wrapper<lsp::vfs::File const> const& file: m_vfs.files())
		validate(file.get());
}

void LanguageServer::validate(lsp::vfs::File const& _file)
{
	PublishDiagnosticsList result;
	validate(_file, result);

	for (lsp::protocol::PublishDiagnosticsParams const& diag: result)
		notify(diag);
}

frontend::ReadCallback::Result LanguageServer::readFile(string const& _kind, string const& _path)
{
	using namespace frontend;

	// TODO: do we need this translation?
	string localPath = _path;
	if (localPath.find("file://") == 0)
		localPath.erase(0, 7);

	try
	{
		if (_kind != ReadCallback::kindString(ReadCallback::Kind::ReadFile))
			return ReadCallback::Result{false, "Invalid readFile callback kind " + _kind};

		// TODO: do we want to make use of m_allowedDirectories?
		// TODO: what iff file does not exist physically on disk? (Web clients? Remix?)
		// TODO: fix ReadCallback::Result to be be either file contents OR an error of given type (std::variant? solidity::Result?)

		if (auto file = m_vfs.find(_path); file != nullptr)
		{
			auto const& contents = file->str();
			m_sourceCodes[localPath] = contents;
			return ReadCallback::Result{true, contents};
		}
		else if (auto i = m_sourceCodes.find(_path); i != end(m_sourceCodes))
			return ReadCallback::Result{true, i->second};
		else
			return ReadCallback::Result{false, "File not found."};

		return frontend::ReadCallback::Result{}; // TODO
	}
	catch (...)
	{
		return ReadCallback::Result{false, "Unahdneld exception caught in readFile callback."};
	}
}

constexpr lsp::protocol::DiagnosticSeverity toDiagnosticSeverity(Error::Type _errorType)
{
	switch (_errorType)
	{
		case Error::Type::CodeGenerationError:
		case Error::Type::DeclarationError:
		case Error::Type::DocstringParsingError:
		case Error::Type::ParserError:
		case Error::Type::SyntaxError:
		case Error::Type::TypeError:
			return lsp::protocol::DiagnosticSeverity::Error;
		case Error::Type::Warning:
			return lsp::protocol::DiagnosticSeverity::Warning;
	}
	// Should never be reached.
	return lsp::protocol::DiagnosticSeverity::Error;
}

void LanguageServer::validate(lsp::vfs::File const& _file, PublishDiagnosticsList& _result)
{
	// TODO
	//
	// 0.) [ ] drop old intermediate data structures (such as AST)
	// 1.) [ ] fully recompile the sources (and collect errors)
	// 2.) [ ] reconstruct m_diagnostics
	// 3.) [ ] push diagnostics to the client

	lsp::protocol::PublishDiagnosticsParams params{};
	params.uri = _file.uri();

	m_sourceCodes.clear();
	m_sourceCodes[_file.uri().substr(7)] = _file.str();

	m_compilerStack = make_unique<CompilerStack>(bind(&LanguageServer::readFile, this, _1, _2));
	// TODO: configure all compiler flags like in CommandLineInterface (TODO: refactor to share logic!)

	OptimiserSettings settings = OptimiserSettings::standard(); // TODO: or OptimiserSettings::minimal(); // configurable
	m_compilerStack->setOptimiserSettings(settings);
	m_compilerStack->setParserErrorRecovery(true);
	m_compilerStack->setEVMVersion(EVMVersion::constantinople()); // TODO: configurable
	m_compilerStack->setRevertStringBehaviour(RevertStrings::Default); // TODO configurable
	m_compilerStack->setSources(m_sourceCodes);
	m_compilerStack->compile();

	for (shared_ptr<Error const> const& error: m_compilerStack->errors())
	{
		auto const message = SourceReferenceExtractor::extract(
			*error,
			(error->type() == Error::Type::Warning) ? "Warning" : "Error"
		);

		auto const severity = toDiagnosticSeverity(error->type());

		// global warnings don't have positions in the source code - TODO: default them to top of file?
		auto const position = LineColumn{{
			max(message.primary.position.line, 0),
			max(message.primary.position.column, 0)
		}};

		lsp::protocol::Diagnostic diag{};

		diag.range.start.line = position.line;
		diag.range.start.column = position.column;
		diag.range.end.line = position.line;
		diag.range.end.column = position.column + 1;
		diag.message = message.primary.message;
		diag.source = "solc";
		diag.severity = severity;
		//diag.code = "42"; // TODO (another PR?)

		params.diagnostics.emplace_back(move(diag));
	}

	// some additional analysis (as proof of concept)
#if 1
	for (size_t pos = _file.str().find("FIXME", 0); pos != string::npos; pos = _file.str().find("FIXME", pos + 1))
	{
		lsp::protocol::Diagnostic diag{};
		diag.message = "Hello, FIXME's should be fixed.";
		diag.range.start = _file.buffer().toPosition(pos);
		diag.range.end = {diag.range.start.line, diag.range.start.column + 5};
		diag.severity = lsp::protocol::DiagnosticSeverity::Error;
		diag.source = "solc";
		params.diagnostics.emplace_back(diag);
	}

	for (size_t pos = _file.str().find("TODO", 0); pos != string::npos; pos = _file.str().find("FIXME", pos + 1))
	{
		lsp::protocol::Diagnostic diag{};
		diag.message = "Please remember to create a ticket on GitHub for that.";
		diag.range.start = _file.buffer().toPosition(pos);
		diag.range.end = {diag.range.start.line, diag.range.start.column + 5};
		diag.severity = lsp::protocol::DiagnosticSeverity::Hint;
		diag.source = "solc";
		params.diagnostics.emplace_back(diag);
	}
#endif

	_result.emplace_back(params);
}

class ASTNodeLocator : public ASTConstVisitor
{
public:
	ASTNodeLocator(lsp::Position const& _pos)
	{
		(void) _pos;
	}

	bool visit(Identifier const& _node) override
	{
		return visitNode(_node);
	}
};

frontend::ASTNode const* LanguageServer::findASTNode(lsp::Position const& _position, std::string const& _fileName)
{
	(void) _position;
	(void) _fileName;

	if (!m_compilerStack)
		return nullptr;

	m_compilerStack->ast(_fileName);
	frontend::ASTNode const& sourceUnit = m_compilerStack->ast(_fileName);
	ASTNodeLocator m{_position};
	sourceUnit.accept(m);

	return nullptr;
}

void LanguageServer::operator()(lsp::protocol::DefinitionParams const& _params)
{
	lsp::protocol::DefinitionReplyParams params{};


	params.uri = _params.textDocument.uri;
	params.range.start.line = _params.position.line + 1;
	params.range.start.column = _params.position.column + 1;
	params.range.end.line = _params.position.line + 1;
	params.range.end.column = _params.position.column + 5;

	reply(_params.requestId, params);
}

} // namespace solidity
