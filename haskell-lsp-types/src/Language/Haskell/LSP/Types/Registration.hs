{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DuplicateRecordFields #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module Language.Haskell.LSP.Types.Registration where

import           Data.Aeson
import           Data.Aeson.TH
import           Data.Text (Text)
import           Data.Function (on)
import           Data.Kind
import           Data.Void (Void)
import           GHC.Generics
import           Language.Haskell.LSP.Types.CodeAction
import           Language.Haskell.LSP.Types.CodeLens
import           Language.Haskell.LSP.Types.Command
import           Language.Haskell.LSP.Types.Common
import           Language.Haskell.LSP.Types.Completion
import           Language.Haskell.LSP.Types.Declaration
import           Language.Haskell.LSP.Types.Definition
import           Language.Haskell.LSP.Types.DocumentColor
import           Language.Haskell.LSP.Types.DocumentHighlight
import           Language.Haskell.LSP.Types.DocumentLink
import           Language.Haskell.LSP.Types.DocumentSymbol
import           Language.Haskell.LSP.Types.FoldingRange
import           Language.Haskell.LSP.Types.Formatting
import           Language.Haskell.LSP.Types.Hover
import           Language.Haskell.LSP.Types.Implementation
import           Language.Haskell.LSP.Types.Method
import           Language.Haskell.LSP.Types.References
import           Language.Haskell.LSP.Types.Rename
import           Language.Haskell.LSP.Types.SignatureHelp
import           Language.Haskell.LSP.Types.SelectionRange
import           Language.Haskell.LSP.Types.TextDocument
import           Language.Haskell.LSP.Types.TypeDefinition
import           Language.Haskell.LSP.Types.Utils
import           Language.Haskell.LSP.Types.WatchedFiles
import           Language.Haskell.LSP.Types.WorkspaceSymbol


-- ---------------------------------------------------------------------

-- | Matches up the registration options for a specific method
type family RegistrationOptions (m :: Method FromClient t) :: Type where
  -- Workspace
  RegistrationOptions WorkspaceDidChangeWorkspaceFolders = Empty
  RegistrationOptions WorkspaceDidChangeConfiguration    = Empty
  RegistrationOptions WorkspaceDidChangeWatchedFiles     = DidChangeWatchedFilesRegistrationOptions
  RegistrationOptions WorkspaceSymbol                    = WorkspaceSymbolRegistrationOptions
  RegistrationOptions WorkspaceExecuteCommand            = ExecuteCommandRegistrationOptions

  -- Text synchronisation
  RegistrationOptions TextDocumentDidOpen                = TextDocumentRegistrationOptions
  RegistrationOptions TextDocumentDidChange              = TextDocumentChangeRegistrationOptions
  RegistrationOptions TextDocumentWillSave               = TextDocumentRegistrationOptions
  RegistrationOptions TextDocumentWillSaveWaitUntil      = TextDocumentRegistrationOptions
  RegistrationOptions TextDocumentDidSave                = TextDocumentSaveRegistrationOptions
  RegistrationOptions TextDocumentDidClose               = TextDocumentRegistrationOptions

  -- Language features
  RegistrationOptions TextDocumentCompletion             = CompletionRegistrationOptions
  RegistrationOptions TextDocumentHover                  = HoverRegistrationOptions
  RegistrationOptions TextDocumentSignatureHelp          = SignatureHelpRegistrationOptions
  RegistrationOptions TextDocumentDeclaration            = DeclarationRegistrationOptions
  RegistrationOptions TextDocumentDefinition             = DefinitionRegistrationOptions
  RegistrationOptions TextDocumentTypeDefinition         = TypeDefinitionRegistrationOptions
  RegistrationOptions TextDocumentImplementation         = ImplementationRegistrationOptions
  RegistrationOptions TextDocumentReferences             = ReferenceRegistrationOptions
  RegistrationOptions TextDocumentDocumentHighlight      = DocumentHighlightRegistrationOptions
  RegistrationOptions TextDocumentDocumentSymbol         = DocumentSymbolRegistrationOptions
  RegistrationOptions TextDocumentCodeAction             = CodeActionRegistrationOptions
  RegistrationOptions TextDocumentCodeLens               = CodeLensRegistrationOptions
  RegistrationOptions TextDocumentDocumentLink           = DocumentLinkRegistrationOptions
  RegistrationOptions TextDocumentDocumentColor          = DocumentColorRegistrationOptions
  RegistrationOptions TextDocumentFormatting             = DocumentFormattingRegistrationOptions
  RegistrationOptions TextDocumentRangeFormatting        = DocumentRangeFormattingRegistrationOptions
  RegistrationOptions TextDocumentOnTypeFormatting       = DocumentOnTypeFormattingRegistrationOptions
  RegistrationOptions TextDocumentRename                 = RenameRegistrationOptions
  RegistrationOptions TextDocumentFoldingRange           = FoldingRangeRegistrationOptions
  RegistrationOptions TextDocumentSelectionRange         = SelectionRangeRegistrationOptions
  RegistrationOptions m                                  = Void

data Registration (m :: Method FromClient t) =
  Registration
    { -- | The id used to register the request. The id can be used to deregister
      -- the request again.
      _id :: Text
      -- | The method / capability to register for.
    , _method :: SClientMethod m
      -- | Options necessary for the registration.
      -- Make this strict to aid the pattern matching exhaustiveness checker
    , _registerOptions :: !(RegistrationOptions m)
    }
  deriving Generic

deriving instance Eq (RegistrationOptions m) => Eq (Registration m)
deriving instance Show (RegistrationOptions m) => Show (Registration m)

-- This generates the function
-- regHelper :: SMethod m
--           -> (( Show (RegistrationOptions m)
--               , ToJSON (RegistrationOptions m)
--               , FromJSON ($regOptTcon m)
--              => x)
--           -> x
makeRegHelper ''RegistrationOptions

instance ToJSON (Registration m) where
  toJSON x@(Registration _ m _) = regHelper m (genericToJSON lspOptions x)

data SomeRegistration = forall t (m :: Method FromClient t). SomeRegistration (Registration m)

instance ToJSON SomeRegistration where
  toJSON (SomeRegistration r) = toJSON r

instance FromJSON SomeRegistration where
  parseJSON = withObject "Registration" $ \o -> do
    SomeClientMethod m <- o .: "method"
    r <- Registration <$> o .: "id" <*> pure m <*> regHelper m (o .: "registerOptions")
    pure (SomeRegistration r)

instance Eq SomeRegistration where
  (==) = (==) `on` toJSON

instance Show SomeRegistration where
  show (SomeRegistration r@(Registration _ m _)) = regHelper m (show r)

data RegistrationParams =
  RegistrationParams { _registrations :: List SomeRegistration }
  deriving (Show, Eq)

deriveJSON lspOptions ''RegistrationParams


-- ---------------------------------------------------------------------

-- | General parameters to unregister a capability.
data Unregistration =
  Unregistration
    { -- | The id used to unregister the request or notification. Usually an id
      -- provided during the register request.
      _id     :: Text
      -- | The method / capability to unregister for.
    , _method :: SomeClientMethod
    } deriving (Show, Eq)

deriveJSON lspOptions ''Unregistration

data UnregistrationParams =
  UnregistrationParams
    { -- | This should correctly be named @unregistrations@. However changing this
      -- is a breaking change and needs to wait until we deliver a 4.x version
      -- of the specification.
      _unregistrations :: List Unregistration
    } deriving (Show, Eq)

deriveJSON lspOptions ''UnregistrationParams
