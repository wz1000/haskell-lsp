{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Language.Haskell.LSP.Types.Initialize where

import Data.Aeson
import Data.Aeson.TH
import Data.Text (Text)
import qualified Data.Text as T
import Language.Haskell.LSP.Types.ClientCapabilities
import Language.Haskell.LSP.Types.Common
import Language.Haskell.LSP.Types.Progress
import Language.Haskell.LSP.Types.ServerCapabilities
import Language.Haskell.LSP.Types.Uri
import Language.Haskell.LSP.Types.Utils
import Language.Haskell.LSP.Types.WorkspaceFolders

data Trace = TraceOff | TraceMessages | TraceVerbose
           deriving (Show, Read, Eq)

instance ToJSON Trace where
  toJSON TraceOff      = String (T.pack "off")
  toJSON TraceMessages = String (T.pack "messages")
  toJSON TraceVerbose  = String (T.pack "verbose")

instance FromJSON Trace where
  parseJSON (String s) = case T.unpack s of
    "off"      -> return TraceOff
    "messages" -> return TraceMessages
    "verbose"  -> return TraceVerbose
    _          -> mempty
  parseJSON _          = mempty

data ClientInfo =
  ClientInfo
  { -- | The name of the client as defined by the client.
    _name    :: Text
    -- | The client's version as defined by the client.
  , _version :: Maybe Text
  } deriving (Show, Read, Eq)
deriveJSON lspOptions ''ClientInfo

makeExtendingDatatype "InitializeParams" [''WorkDoneProgressParams]
  [ ("_processId",             [t| Maybe Int|])
  , ("_clientInfo",            [t| Maybe ClientInfo |])
  , ("_rootPath",              [t| Maybe Text |])
  , ("_rootUri",               [t| Maybe Uri  |])
  , ("_initializationOptions", [t| Maybe Value |])
  , ("_capabilities",          [t| ClientCapabilities |])
  , ("_trace",                 [t| Maybe Trace |])
  , ("_workspaceFolders",      [t| Maybe (List WorkspaceFolder) |])
  ]

{-# DEPRECATED _rootPath "Use _rootUri" #-}

deriveJSON lspOptions ''InitializeParams

data InitializeError =
  InitializeError
    { _retry :: Bool
    } deriving (Read, Show, Eq)

deriveJSON lspOptions ''InitializeError

data ServerInfo =
  ServerInfo
  { -- | The name of the server as defined by the server.
    _name    :: Text
    -- | The server's version as defined by the server.
  , _version :: Maybe Text
  } deriving (Show, Read, Eq)
deriveJSON lspOptions ''ServerInfo

data InitializeResult =
  InitializeResult
  { -- | The capabilities the language server provides.
    _capabilities :: ServerCapabilities
    -- | Information about the server.
    -- Since LSP 3.15.0
  , _serverInfo   :: Maybe ServerInfo
  } deriving (Show, Read, Eq)

deriveJSON lspOptions ''InitializeResult

-- ---------------------------------------------------------------------

data InitializedParams =
  InitializedParams
  {
  } deriving (Show, Read, Eq)

instance FromJSON InitializedParams where
  parseJSON (Object _) = pure InitializedParams
  parseJSON _            = mempty

instance ToJSON InitializedParams where
  toJSON InitializedParams = Object mempty

