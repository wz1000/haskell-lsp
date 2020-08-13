{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Language.Haskell.LSP.Types.Formatting where

import Data.Aeson.TH
import Data.Text (Text)
import Language.Haskell.LSP.Types.Location
import Language.Haskell.LSP.Types.Progress
import Language.Haskell.LSP.Types.TextDocument
import Language.Haskell.LSP.Types.Utils

data DocumentFormattingClientCapabilities =
  DocumentFormattingClientCapabilities
    { -- | Whether formatting supports dynamic registration.
      _dynamicRegistration :: Maybe Bool
    } deriving (Show, Read, Eq)
deriveJSON lspOptions ''DocumentFormattingClientCapabilities

makeExtendingDatatype "DocumentFormattingOptions" [''WorkDoneProgressOptions] []
deriveJSON lspOptions ''DocumentFormattingOptions

makeExtendingDatatype "DocumentFormattingRegistrationOptions"
  [ ''TextDocumentRegistrationOptions,
    ''DocumentFormattingOptions
  ]
  []
deriveJSON lspOptions ''DocumentFormattingRegistrationOptions

-- | Value-object describing what options formatting should use.
data FormattingOptions = FormattingOptions
  { -- | Size of a tab in spaces.
    _tabSize :: Int,
    -- | Prefer spaces over tabs
    _insertSpaces :: Bool,
    -- | Trim trailing whitespace on a line.
    --
    -- Since LSP 3.15.0
    _trimTrailingWhitespace :: Maybe Bool,
    -- | Insert a newline character at the end of the file if one does not exist.
    --
    -- Since LSP 3.15.0
    _insertFinalNewline :: Maybe Bool,
    -- | Trim all newlines after the final newline at the end of the file.
    -- 
    -- Since LSP 3.15.0
    _trimFinalNewlines :: Maybe Bool
    -- Note: May be more properties
  }
  deriving (Read, Show, Eq)

deriveJSON lspOptions ''FormattingOptions
makeExtendingDatatype "DocumentFormattingParams" [''WorkDoneProgressParams]
  [ ("_textDocument", [t| TextDocumentIdentifier |])
  , ("_options", [t| FormattingOptions |])
  ]
deriveJSON lspOptions ''DocumentFormattingParams

-- -------------------------------------

data DocumentRangeFormattingClientCapabilities =
  DocumentRangeFormattingClientCapabilities
    { -- | Whether formatting supports dynamic registration.
      _dynamicRegistration :: Maybe Bool
    } deriving (Show, Read, Eq)
deriveJSON lspOptions ''DocumentRangeFormattingClientCapabilities

makeExtendingDatatype "DocumentRangeFormattingOptions" [''WorkDoneProgressOptions] []
deriveJSON lspOptions ''DocumentRangeFormattingOptions

makeExtendingDatatype "DocumentRangeFormattingRegistrationOptions"
  [ ''TextDocumentRegistrationOptions
  , ''DocumentRangeFormattingOptions
  ]
  []
deriveJSON lspOptions ''DocumentRangeFormattingRegistrationOptions

makeExtendingDatatype "DocumentRangeFormattingParams" [''WorkDoneProgressParams]
  [ ("_textDocument", [t| TextDocumentIdentifier |])
  , ("_range", [t| Range |])
  , ("_options", [t| FormattingOptions |])
  ]
deriveJSON lspOptions ''DocumentRangeFormattingParams

-- -------------------------------------

data DocumentOnTypeFormattingClientCapabilities =
  DocumentOnTypeFormattingClientCapabilities
    { -- | Whether formatting supports dynamic registration.
      _dynamicRegistration :: Maybe Bool
    } deriving (Show, Read, Eq)
deriveJSON lspOptions ''DocumentOnTypeFormattingClientCapabilities

data DocumentOnTypeFormattingOptions =
  DocumentOnTypeFormattingOptions
    { -- | A character on which formatting should be triggered, like @}@.
      _firstTriggerCharacter :: Text
    , -- | More trigger characters.
      _moreTriggerCharacter  :: Maybe [Text]
    } deriving (Read,Show,Eq)
deriveJSON lspOptions ''DocumentOnTypeFormattingOptions

makeExtendingDatatype "DocumentOnTypeFormattingRegistrationOptions"
  [ ''TextDocumentRegistrationOptions
  , ''DocumentOnTypeFormattingOptions
  ]
  []
deriveJSON lspOptions ''DocumentOnTypeFormattingRegistrationOptions

makeExtendingDatatype "DocumentOnTypeFormattingParams" [''TextDocumentPositionParams]
  [ ("_ch", [t| String |])
  , ("_options", [t| FormattingOptions |])
  ]
deriveJSON lspOptions ''DocumentOnTypeFormattingParams
