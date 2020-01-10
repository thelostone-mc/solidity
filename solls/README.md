# Solidity: Language Server

## Motivations

The following features could be implemented (incomplete list of ideas):

- realtime compilation validation (error, warning, formal verification)
- auto completion
- go to definition
- find all references
- auto correction on typical programming issues
- semantic highlying of symbols
- symbol rename
- automatic adding of imports whenever a symbol is referenced that is not yet imported in the current unit.
- signature and natspec documentation information upon symbol hover
  - show generated EVM code for hovered scope
  - show estimated gas cost for hovered expression
- get realtime suggestions to improve code quality, or other reasons
- the solidity upgrade tool could potentially be integrated into the language server
- also support Yul

### Questions:

- what clients would you guys like us to support? Remix, VS, VIM, ...?
- could this be wanted by by Remix?
- what would be most/least important to you to have in general (and in the initial release)
  - compiler diagnostics
  - auto completion (requires some compiler stack refactoring to allow invalid ASTs)
  - goto definition / implementation
  - find all references
  - text folding
  - symbol rename
  - semantic highlight
  - (on-type) text formatting
  - ... fast responding high performant LS
- how do clients want to push their build configuration to the server?
  - C++ LS uses a `compile_commands.json` for the flags
- Since the LS is internally compiling the code, it might as well extend the API by
  also responding to compilation results (on successful builds).
- LSIF: is there interest in "Language Server Index Format"?
  - pronounced "else-if"
  - Ref: https://code.visualstudio.com/blogs/2019/02/19/lsif
  - this is an indexing file format that the LS can produce for offline usage
  - example use: platforms (such as GitHub!) could provide goto definition (etc) features

## What an initial release could look like

### Features:

- [ ] basic compilation checking with reporting errors to the client
- [ ] goto definition
- [ ] semantic highlighting of the currently selected word
- [ ] hover support (showing signature, maybe natspec docs already?)
- [ ] auto completion upon writing `.` or `(` or `,`

### Internal Requirements

- [ ] (WIP) unit tests for all LSP core functionalities
- [ ] validation runs (look for compilation errors/warnings)
- [ ] Publish Notifications to the clients
- [ ] Completion Requests
- [ ] hover-information (signature + natspec documentation)
- [ ] perform validation not after every change but
  - either if there was no text change notification for a given timeout, or
  - if a bigger timeout has been exceeded and no revalidation has been taken place since that period of time yet.

### impl TODO checklist

- [x] detail: basic functioning JSON-RPC
- [x] detail: (WIP) translation from/to JSON-RPC <-> higher level structs
- [x] detail: buffer management ("text synchronization")

### methods:

- [ ] client/registerCapability
- [ ] client/unregisterCapability
- [ ] codeLens/resolve
- [ ] completionItem/resolve (-> method)
- [ ] documentLink/resolve
- [x] exit (-> notification)
- [x] initialize (-> method)
- [x] initialized (-> notification)
- [x] shutdown (-> notification)
- [ ] telemetry/event
- [ ] textDocument/codeAction
- [ ] textDocument/codeLens
- [ ] textDocument/colorPresentation
- [ ] textDocument/completion (-> method)
- [ ] textDocument/declaration (-> method) XXX
- [ ] textDocument/definition (-> method) XXX
- [x] textDocument/didChange (-> notification)
- [x] textDocument/didClose (-> notification)
- [x] textDocument/didOpen (-> notification)
- [ ] textDocument/didSave (-> notification)
- [ ] textDocument/documentColor
- [ ] textDocument/documentHighlight (-> method) XXX
- [ ] textDocument/documentLink
- [ ] textDocument/documentSymbol (-> method)
- [ ] textDocument/foldingRange
- [ ] textDocument/formatting
- [ ] textDocument/hover (-> method) XXX
- [ ] textDocument/implementation (-> method) XXX
- [ ] textDocument/onTypeFormatting
- [ ] textDocument/prepareRename
- [ ] textDocument/publishDiagnostics (<- notification) XXX
- [ ] textDocument/rangeFormatting
- [ ] textDocument/references (-> method) XXX
- [ ] textDocument/rename
- [ ] textDocument/selectionRange
- [ ] textDocument/signatureHelp (-> method) XXX
- [ ] textDocument/typeDefinition (-> method) XXX
- [ ] textDocument/willSave (-> notification)
- [ ] textDocument/willSaveWaitUntil (-> method)
- [x] window/logMessage (<- notification)
- [ ] window/showMessage
- [ ] window/showMessageRequest
- [ ] window/workDoneProgress/cancel
- [ ] window/workDoneProgress/create
- [ ] workspace/applyEdit
- [ ] workspace/configuration
- [ ] workspace/didChangeConfiguration (-> method)
- [ ] workspace/didChangeWatchedFiles
- [ ] workspace/didChangeWorkspaceFolders (-> notification)
- [ ] workspace/executeCommand
- [ ] workspace/symbol

