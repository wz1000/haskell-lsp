{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Haskell.LSP.TH.DataTypesJSON where

import Data.Aeson.TH
import qualified Data.Aeson as A
import qualified Data.HashMap.Strict as H
import qualified Data.Text as T

import Data.Monoid
import Language.Haskell.LSP.Utility
import Data.Default

-- ---------------------------------------------------------------------
{-
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#position

Position in a text document expressed as zero-based line and character offset. A
position is between two characters like an 'insert' cursor in a editor.

interface Position {
    /**
     * Line position in a document (zero-based).
     */
    line: number;

    /**
     * Character offset on a line in a document (zero-based).
     */
    character: number;
}
-}
data Position =
  Position
    { linePosition       :: Int
    , characterPosition  :: Int
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "Position") } ''Position)

instance Default Position where
  def = Position def def

-- ---------------------------------------------------------------------
{-
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#range

A range in a text document expressed as (zero-based) start and end positions. A
range is comparable to a selection in an editor. Therefore the end position is
exclusive.

interface Range {
    /**
     * The range's start position.
     */
    start: Position;

    /**
     * The range's end position.
     */
    end: Position;
}
-}

data Range =
  Range
    { startRange :: Position
    , endRange   :: Position
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "Range") } ''Range)

instance Default Range where
  def = Range def def

-- ---------------------------------------------------------------------
{-
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#location

Represents a location inside a resource, such as a line inside a text file.

interface Location {
    uri: string;
    range: Range;
}
-}

data Location =
  Location
    { uriLocation   :: String
    , rangeLocation :: Range
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "Location") } ''Location)

instance Default Location where
  def = Location def def

-- ---------------------------------------------------------------------
{-
The protocol currently supports the following diagnostic severities:

enum DiagnosticSeverity {
    /**
     * Reports an error.
     */
    Error = 1,
    /**
     * Reports a warning.
     */
    Warning = 2,
    /**
     * Reports an information.
     */
    Information = 3,
    /**
     * Reports a hint.
     */
    Hint = 4
}
-}
data DiagnosticSeverity = DsError  -- ^ Error = 1,
                 | DsWarning -- ^ Warning = 2,
                 | DsInfo    -- ^ Info = 3,
                 | DsHint     -- ^ Hint = 4
        deriving (Eq,Ord,Show,Read,Enum)

instance A.ToJSON DiagnosticSeverity where
  toJSON DsError   = A.Number 1
  toJSON DsWarning = A.Number 2
  toJSON DsInfo    = A.Number 3
  toJSON DsHint    = A.Number 4

instance A.FromJSON DiagnosticSeverity where
  parseJSON (A.Number 1) = pure DsError
  parseJSON (A.Number 2) = pure DsWarning
  parseJSON (A.Number 3) = pure DsInfo
  parseJSON (A.Number 4) = pure DsHint
  parseJSON _            = mempty

instance Default DiagnosticSeverity where
  def = DsError

-- ---------------------------------------------------------------------
{-
Diagnostic

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#diagnostic

Represents a diagnostic, such as a compiler error or warning. Diagnostic objects
are only valid in the scope of a resource.

interface Diagnostic {
    /**
     * The range at which the message applies.
     */
    range: Range;

    /**
     * The diagnostic's severity. Can be omitted. If omitted it is up to the
     * client to interpret diagnostics as error, warning, info or hint.
     */
    severity?: number;

    /**
     * The diagnostic's code. Can be omitted.
     */
    code?: number | string;

    /**
     * A human-readable string describing the source of this
     * diagnostic, e.g. 'typescript' or 'super lint'.
     */
    source?: string;

    /**
     * The diagnostic's message.
     */
    message: string;
}
-}
data Diagnostic =
  Diagnostic
    {  rangeDiagnostic   :: Range
    , severityDiagnostic :: DiagnosticSeverity
    , codeDiagnostic     :: Int
    , sourceDiagnostic   :: String
    , messageDiagnostic  :: String
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "Diagnostic") } ''Diagnostic)

instance Default Diagnostic where
  def = Diagnostic def def 0 "" ""

-- ---------------------------------------------------------------------
{-
Command

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#command

Represents a reference to a command. Provides a title which will be used to
represent a command in the UI. Commands are identitifed using a string
identifier and the protocol currently doesn't specify a set of well known
commands. So executing a command requires some tool extension code.

interface Command {
    /**
     * Title of the command, like `save`.
     */
    title: string;
    /**
     * The identifier of the actual command handler.
     */
    command: string;
    /**
     * Arguments that the command handler should be
     * invoked with.
     */
    arguments?: any[];
}
-}

data Command =
  Command
    { titleCommand    :: String
    , commandCommand   :: String
    , argumentsCommand :: Maybe A.Object
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "Command") } ''Command)

instance Default Command where
  def = Command "" "" Nothing

-- ---------------------------------------------------------------------
{-
TextEdit

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#textedit

A textual edit applicable to a text document.

interface TextEdit {
    /**
     * The range of the text document to be manipulated. To insert
     * text into a document create a range where start === end.
     */
    range: Range;

    /**
     * The string to be inserted. For delete operations use an
     * empty string.
     */
    newText: string;
}
-}

data TextEdit =
  TextEdit
    { rangeTextEdit   :: Range
    , newTextTextEdit :: String
    } deriving (Show,Read,Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TextEdit") } ''TextEdit)

instance Default TextEdit where
  def = TextEdit def def

-- ---------------------------------------------------------------------
{-
WorkspaceEdit

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#workspaceedit

A workspace edit represents changes to many resources managed in the workspace.

interface WorkspaceEdit {
    /**
     * Holds changes to existing resources.
     */
    changes: { [uri: string]: TextEdit[]; };
}
-}

type WorkspaceEditMap = H.HashMap T.Text [TextEdit]

instance Default (H.HashMap T.Text [TextEdit]) where
  def = mempty

data WorkspaceEdit =
  WorkspaceEdit
    { changesWorkspaceEdit :: WorkspaceEditMap
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "WorkspaceEdit") } ''WorkspaceEdit)

instance Default WorkspaceEdit where
  def = WorkspaceEdit def

-- ---------------------------------------------------------------------
{-
TextDocumentIdentifier

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#textdocumentidentifier

Text documents are identified using a URI. On the protocol level, URIs are
passed as strings. The corresponding JSON structure looks like this:

interface TextDocumentIdentifier {
    /**
     * The text document's URI.
     */
    uri: string;
}
-}
data TextDocumentIdentifier =
  TextDocumentIdentifier
    { uriTextDocumentIdentifier :: String
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TextDocumentIdentifier") } ''TextDocumentIdentifier)

instance Default TextDocumentIdentifier where
  def = TextDocumentIdentifier def

-- ---------------------------------------------------------------------

{-
TextDocumentItem

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#textdocumentitem

    New: An item to transfer a text document from the client to the server.

interface TextDocumentItem {
    /**
     * The text document's URI.
     */
    uri: string;

    /**
     * The text document's language identifier.
     */
    languageId: string;

    /**
     * The version number of this document (it will strictly increase after each
     * change, including undo/redo).
     */
    version: number;

    /**
     * The content of the opened text document.
     */
    text: string;
}
-}

data TextDocumentItem =
  TextDocumentItem {
    uriTextDocumentItem        :: String
  , languageIdTextDocumentItem :: String
  , versionTextDocumentItem    :: Int
  , textTextDocumentItem       :: String
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TextDocumentItem") } ''TextDocumentItem)

-- ---------------------------------------------------------------------
{-
VersionedTextDocumentIdentifier

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#versionedtextdocumentidentifier

    New: An identifier to denote a specific version of a text document.

interface VersionedTextDocumentIdentifier extends TextDocumentIdentifier {
    /**
     * The version number of this document.
     */
    version: number;
-}
data VersionedTextDocumentIdentifier =
  VersionedTextDocumentIdentifier
    { uriVersionedTextDocumentIdentifier     :: String
    , versionVersionedTextDocumentIdentifier :: Int
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "VersionedTextDocumentIdentifier") } ''VersionedTextDocumentIdentifier)

instance Default VersionedTextDocumentIdentifier where
  def = VersionedTextDocumentIdentifier def def

-- ---------------------------------------------------------------------
{-
TextDocumentPositionParams

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#textdocumentpositionparams

    Changed: Was TextDocumentPosition in 1.0 with inlined parameters


interface TextDocumentPositionParams {
    /**
     * The text document.
     */
    textDocument: TextDocumentIdentifier;

    /**
     * The position inside the text document.
     */
    position: Position;
}

-}
data TextDocumentPositionParams =
  TextDocumentPositionParams
    { textDocumentTextDocumentPositionParams :: TextDocumentIdentifier
    , positionTextDocumentPositionParams     :: Position
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TextDocumentPositionParams") } ''TextDocumentPositionParams)

instance Default TextDocumentPositionParams where
  def = TextDocumentPositionParams def def


-- =====================================================================
-- ACTUAL PROTOCOL -----------------------------------------------------
-- =====================================================================

-- ---------------------------------------------------------------------
{-
Initialize Request

https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#initialize-request

The initialize request is sent as the first request from the client to the server.

Request

    method: 'initialize'
    params: InitializeParams defined as follows:

interface InitializeParams {
    /**
     * The process Id of the parent process that started
     * the server.
     */
    processId: number;

    /**
     * The rootPath of the workspace. Is null
     * if no folder is open.
     */
    rootPath: string;

    /**
     * User provided initialization options.
     */
    initializationOptions?: any;

    /**
     * The capabilities provided by the client (editor)
     */
    capabilities: ClientCapabilities;
}
-}

data InitializeRequestArguments =
  InitializeRequestArguments {
    processIdInitializeRequestArguments    :: Int
  , rootPathInitializeRequestArguments     :: Maybe String
  , capabilitiesInitializeRequestArguments :: A.Object -- None currently defined, but empty object sent
  , initializationOptionsInitializeRequestArguments :: Maybe A.Object
  , traceInitializeRequestArguments        :: String -- observed to be present in the wild
  } deriving (Show, Read, Eq)


$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "InitializeRequestArguments") } ''InitializeRequestArguments)

instance Default InitializeRequestArguments where
  def = InitializeRequestArguments 0 mempty mempty mempty mempty

-- ---------------------------------------------------------------------

-- |
--   Client-initiated request
--

-- {"jsonrpc":"2.0","id":0,"method":"initialize","params":{"processId":1749,"capabilities":{},"trace":"off"}}
-- {"jsonrpc":"2.0","id":0,"method":"initialize","params":{"processId":17554,"rootPath":"/home/alanz/mysrc/github/alanz/haskell-lsp","capabilities":{},"trace":"off"}}
data InitializeRequest =
  InitializeRequest {
    idInitializeRequest       :: Int                         -- Sequence number
  , paramsInitializeRequest   :: InitializeRequestArguments  -- Object containing arguments for the command
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "InitializeRequest") } ''InitializeRequest)

instance Default InitializeRequest where
  def = InitializeRequest 0 def

-- ---------------------------------------------------------------------

-- |
--   Information about the capabilities of a language server
--
data InitializeResponseCapabilitiesInner =
  InitializeResponseCapabilitiesInner {
    definitionProviderInitializeResponseCapabilitiesInner :: Bool
  , renameProviderInitializeResponseCapabilitiesInner     :: Bool
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "InitializeResponseCapabilitiesInner") } ''InitializeResponseCapabilitiesInner)

-- |
--
defaultInitializeResponseCapabilitiesInner :: InitializeResponseCapabilitiesInner
defaultInitializeResponseCapabilitiesInner = InitializeResponseCapabilitiesInner True True

-- ---------------------------------------------------------------------
-- |
--   Information about the capabilities of a language server
--
data InitializeResponseCapabilities =
  InitializeResponseCapabilities {
    capabilitiesInitializeResponseCapabilities :: InitializeResponseCapabilitiesInner
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "InitializeResponseCapabilities") } ''InitializeResponseCapabilities)

-- |
--
defaultInitializeResponseCapabilities :: InitializeResponseCapabilities
defaultInitializeResponseCapabilities = InitializeResponseCapabilities defaultInitializeResponseCapabilitiesInner

-- ---------------------------------------------------------------------

-- |
--   Server-initiated response to client request
--
data InitializeResponse =
  InitializeResponse {
    jsonrpcInitializeResponse    :: String
  , idInitializeResponse         :: Int     -- Sequence number
  , resultInitializeResponse     :: InitializeResponseCapabilities  -- The capabilities of this debug adapter
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "InitializeResponse") } ''InitializeResponse)


-- |
--
parseErrorInitializeResponse :: Int -> String -> InitializeResponse
parseErrorInitializeResponse seq msg =
  InitializeResponse  "2.0" seq defaultInitializeResponseCapabilities

-- |
--
errorInitializeResponse :: InitializeRequest -> String -> InitializeResponse
errorInitializeResponse (InitializeRequest reqSeq _) msg =
  InitializeResponse "2.0" reqSeq defaultInitializeResponseCapabilities


{-
Where the type is defined as follows:

enum MessageType {
    /**
     * An error message.
     */
    Error = 1,
    /**
     * A warning message.
     */
    Warning = 2,
    /**
     * An information message.
     */
    Info = 3,
    /**
     * A log message.
     */
    Log = 4
}
-}
data MessageType = MtError   -- ^ Error = 1,
                 | MtWarning -- ^ Warning = 2,
                 | MtInfo    -- ^ Info = 3,
                 | MtLog     -- ^ Log = 4
        deriving (Eq,Ord,Show,Read,Enum)

instance A.ToJSON MessageType where
  toJSON MtError   = A.Number 1
  toJSON MtWarning = A.Number 2
  toJSON MtInfo    = A.Number 3
  toJSON MtLog     = A.Number 4

instance A.FromJSON MessageType where
  parseJSON (A.Number 1) = pure MtError
  parseJSON (A.Number 2) = pure MtWarning
  parseJSON (A.Number 3) = pure MtInfo
  parseJSON (A.Number 4) = pure MtLog
  parseJSON _            = mempty


data DefinitionRequestParams =
  DefinitionRequestParams
    { textDocumentDefinitionRequestParams :: TextDocumentIdentifier
    , positionDefinitionRequestParams     :: Position
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DefinitionRequestParams") } ''DefinitionRequestParams)

instance Default DefinitionRequestParams where
  def = DefinitionRequestParams def def

-- |
--   Client-initiated request
--

-- {"jsonrpc":"2.0","id":1,"method":"textDocument/definition","params":{"textDocument":{"uri":"file:///tmp/Foo.hs"},"position":{"line":1,"character":8}}}
data DefinitionRequest =
  DefinitionRequest {
    idDefinitionRequest       :: Int
  , paramsDefinitionRequest   :: DefinitionRequestParams
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DefinitionRequest") } ''DefinitionRequest)

defaultDefinitionRequest :: DefinitionRequest
defaultDefinitionRequest = DefinitionRequest 0 def

-- ---------------------------------------------------------------------

-- |
--   Server-initiated response to client request
--
data DefinitionResponse =
  DefinitionResponse {
    jsonrpcDefinitionResponse    :: String
  , idDefinitionResponse         :: Int     -- Sequence number
  , resultDefinitionResponse     :: Location
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DefinitionResponse") } ''DefinitionResponse)


-- |
--
parseErrorDefinitionResponse :: Int -> String -> DefinitionResponse
parseErrorDefinitionResponse seq msg =
  DefinitionResponse  "2.0" seq def

-- |
--
errorDefinitionResponse :: DefinitionRequest -> String -> DefinitionResponse
errorDefinitionResponse (DefinitionRequest reqSeq _) msg =
  DefinitionResponse "2.0" reqSeq def

-- ---------------------------------------------------------------------

data RenameRequestParams =
  RenameRequestParams
    { textDocumentRenameRequestParams :: TextDocumentIdentifier
    , positionRenameRequestParams     :: Position
    , newNameRenameRequestParams      :: String
    } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "RenameRequestParams") } ''RenameRequestParams)

instance Default RenameRequestParams where
  def = RenameRequestParams def def def

-- |
--   Client-initiated request
--

-- {\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":{\"uri\":\"file:///home/alanz/mysrc/github/alanz/haskell-lsp/src/HieVscode.hs\"},\"position\":{\"line\":37,\"character\":17},\"newName\":\"getArgs'\"}}
data RenameRequest =
  RenameRequest {
    idRenameRequest       :: Int
  , paramsRenameRequest   :: RenameRequestParams
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "RenameRequest") } ''RenameRequest)

defaultRenameRequest :: RenameRequest
defaultRenameRequest = RenameRequest 0 def

-- ---------------------------------------------------------------------

-- |
--   Server-initiated response to client request
--
data RenameResponse =
  RenameResponse {
    jsonrpcRenameResponse    :: String
  , idRenameResponse         :: Int     -- Sequence number
  , resultRenameResponse     :: Location
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "RenameResponse") } ''RenameResponse)


-- |
--
parseErrorRenameResponse :: Int -> String -> RenameResponse
parseErrorRenameResponse seq msg =
  RenameResponse  "2.0" seq def

-- |
--
errorRenameResponse :: RenameRequest -> String -> RenameResponse
errorRenameResponse (RenameRequest reqSeq _) msg =
  RenameResponse "2.0" reqSeq def

-- ---------------------------------------------------------------------

-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data DidChangeConfigurationParamsNotificationParams =
  DidChangeConfigurationParamsNotificationParams {
    settingsDidChangeConfigurationParamsNotificationParams :: A.Object
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DidChangeConfigurationParamsNotificationParams") } ''DidChangeConfigurationParamsNotificationParams)

defaultDidChangeConfigurationParamsNotificationParams :: DidChangeConfigurationParamsNotificationParams
defaultDidChangeConfigurationParamsNotificationParams = DidChangeConfigurationParamsNotificationParams mempty

-- ---------------------------------------
-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data DidChangeConfigurationParamsNotification =
  DidChangeConfigurationParamsNotification {
    paramsDidChangeConfigurationParamsNotification :: DidChangeConfigurationParamsNotificationParams
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DidChangeConfigurationParamsNotification") } ''DidChangeConfigurationParamsNotification)

defaultDidChangeConfigurationParamsNotification :: DidChangeConfigurationParamsNotification
defaultDidChangeConfigurationParamsNotification = DidChangeConfigurationParamsNotification defaultDidChangeConfigurationParamsNotificationParams

-- ---------------------------------------------------------------------
-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data DidOpenTextDocumentNotificationParams =
  DidOpenTextDocumentNotificationParams {
    textDocumentDidOpenTextDocumentNotificationParams :: TextDocumentItem
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DidOpenTextDocumentNotificationParams") } ''DidOpenTextDocumentNotificationParams)

-- ---------------------------------------
-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data DidOpenTextDocumentNotification =
  DidOpenTextDocumentNotification {
    paramsDidOpenTextDocumentNotification :: DidOpenTextDocumentNotificationParams
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "DidOpenTextDocumentNotification") } ''DidOpenTextDocumentNotification)

-- defaultDidOpenTextDocumentNotification :: DidOpenTextDocumentNotification
-- defaultDidOpenTextDocumentNotification = DidOpenTextDocumentNotification defaultDidOpenTextDocumentNotificationParams

-- ---------------------------------------------------------------------

-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data ExitNotification =
  ExitNotification {
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "ExitNotification") } ''ExitNotification)

defaultExitNotification :: ExitNotification
defaultExitNotification = ExitNotification

-- ---------------------------------------------------------------------

-- |
--   Event message for "output" event type. The event indicates that the target has produced output.
--
data OutputEventBody =
  OutputEventBody {
    categoryOutputEventBody :: String        -- The category of output (such as: 'console', 'stdout', 'stderr', 'telemetry'). If not specified, 'console' is assumed. 
  , outputOutputEventBody   :: String        -- The output to report.
  , dataOutputEventBody     :: Maybe String  -- Optional data to report. For the 'telemetry' category the data will be sent to telemetry, for the other categories the data is shown in JSON format.
  } deriving (Show, Read, Eq)


$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "OutputEventBody") } ''OutputEventBody)

defaultOutputEventBody :: OutputEventBody
defaultOutputEventBody = OutputEventBody "console" "" Nothing

-- ---------------------------------------------------------------------

-- |
--   Event message for "output" event type. The event indicates that the target has produced output.
--
data OutputEvent =
  OutputEvent {
    seqOutputEvent   :: Int     -- Sequence number
  , typeOutputEvent  :: String  -- One of "request", "response", or "event"
  , eventOutputEvent :: String  -- Type of event
  , bodyOutputEvent  :: OutputEventBody 
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "OutputEvent") } ''OutputEvent)

defaultOutputEvent :: Int -> OutputEvent
defaultOutputEvent resSeq = OutputEvent resSeq "event" "output" defaultOutputEventBody

-- ---------------------------------------------------------------------

-- |
--   Client-initiated request
--
data Request =
  Request {
    methodRequest   :: String    -- The command to execute
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "Request") } ''Request)

-- ---------------------------------------------------------------------

-- |
--   Client-initiated request
--
data ErrorResponse =
  ErrorResponse {
    jsonrpcErrorResponse :: String    -- Always "2.0"
  , idErrorResponse      :: Int -- Original request id
  , errorErrorResponse   :: String
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "ErrorResponse") } ''ErrorResponse)

instance Default ErrorResponse where
  def = ErrorResponse "2.0" 0 ""


-- ---------------------------------------------------------------------

-- |
--   Client-initiated request
--

data ShutdownRequest =
  ShutdownRequest {
    idShutdownRequest       :: Int                         -- Sequence number
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "ShutdownRequest") } ''ShutdownRequest)

defaultShutdownRequest :: ShutdownRequest
defaultShutdownRequest = ShutdownRequest 0

-- ---------------------------------------------------------------------

-- |
--   Server-initiated response to client request
--
data ShutdownResponse =
  ShutdownResponse {
    jsonrpcShutdownResponse    :: String
  , idShutdownResponse         :: Int     -- Sequence number
  , resultShutdownResponse     :: String
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "ShutdownResponse") } ''ShutdownResponse)


-- |
--
parseErrorShutdownResponse :: Int -> String -> ShutdownResponse
parseErrorShutdownResponse seq msg =
  ShutdownResponse  "2.0" seq msg

-- |
--
errorShutdownResponse :: Int -> ShutdownRequest -> String -> ShutdownResponse
errorShutdownResponse seq (ShutdownRequest reqSeq) msg =
  ShutdownResponse "2.0" seq msg

-- ---------------------------------------------------------------------

-- |
--   Event message for "terminated" event types.
-- The event indicates that debugging of the debuggee has terminated.
--
data TerminatedEventBody =
  TerminatedEventBody {
    restartTerminatedEventBody :: Bool  -- A debug adapter may set 'restart' to true to request that the front end restarts the session.
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TerminatedEventBody") } ''TerminatedEventBody)

defaultTerminatedEventBody :: TerminatedEventBody
defaultTerminatedEventBody = TerminatedEventBody False

-- ---------------------------------------------------------------------

-- |
--   Event message for "terminated" event types.
--   The event indicates that debugging of the debuggee has terminated.
--
data TerminatedEvent =
  TerminatedEvent {
    seqTerminatedEvent   :: Int     -- Sequence number
  , typeTerminatedEvent  :: String  -- One of "request", "response", or "event"
  , eventTerminatedEvent :: String  -- Type of event
  , bodyTerminatedEvent  :: TerminatedEventBody
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TerminatedEvent") } ''TerminatedEvent)

defaultTerminatedEvent :: Int -> TerminatedEvent
defaultTerminatedEvent seq = TerminatedEvent seq "event" "terminated" defaultTerminatedEventBody

-- ---------------------------------------------------------------------

-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data TraceNotificationParams =
  TraceNotificationParams {
    valueTraceNotificationParams :: String
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TraceNotificationParams") } ''TraceNotificationParams)

defaultTraceNotificationParams :: TraceNotificationParams
defaultTraceNotificationParams = TraceNotificationParams mempty

-- ---------------------------------------
-- |
--   Notification from the server to actually exit now, after shutdown acked
--
data TraceNotification =
  TraceNotification {
    paramsTraceNotification :: TraceNotificationParams
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "TraceNotification") } ''TraceNotification)

defaultTraceNotification :: TraceNotification
defaultTraceNotification = TraceNotification defaultTraceNotificationParams

-- ---------------------------------------------------------------------
{-
The log message notification is sent from the server to the client to ask the
client to log a particular message.

Notification:

    method: 'window/logMessage'
    params: LogMessageParams defined as follows:

interface LogMessageParams {
    /**
     * The message type. See {@link MessageType}
     */
    type: number;

    /**
     * The actual message
     */
    message: string;
}
-}

-- |
--
data MessageNotificationParams =
  MessageNotificationParams {
    typeMessageNotificationParams    :: MessageType
  , messageMessageNotificationParams :: String
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "MessageNotificationParams") } ''MessageNotificationParams)

instance Default MessageNotificationParams where
  def = MessageNotificationParams MtWarning ""

-- ---------------------------------------
-- |
--
data MessageNotification =
  MessageNotification {
    jsonrpcMessageNotification :: String
  , methodMessageNotification  :: String
  , paramsMessageNotification  :: MessageNotificationParams
  } deriving (Show, Read, Eq)

$(deriveJSON defaultOptions { fieldLabelModifier = rdrop (length "MessageNotification") } ''MessageNotification)

-- -------------------------------------

type LogMessageNotification = MessageNotification

instance Default LogMessageNotification where
  def = MessageNotification "2.0" "window/logMessage" def

-- -------------------------------------
{-
The show message notification is sent from a server to a client to ask the
client to display a particular message in the user interface.

Notification:

    method: 'window/showMessage'
    params: ShowMessageParams defined as follows:

interface ShowMessageParams {
    /**
     * The message type. See {@link MessageType}.
     */
    type: number;

    /**
     * The actual message.
     */
    message: string;
}
-}


defLogMessage :: MessageType -> String -> MessageNotification
defLogMessage mt msg = MessageNotification "2.0" "window/logMessage"   (MessageNotificationParams mt msg)

defShowMessage :: MessageType -> String -> MessageNotification
defShowMessage mt msg = MessageNotification "2.0" "window/showMessage" (MessageNotificationParams mt msg)

-- ---------------------------------------------------------------------
