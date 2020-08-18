{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Language.Haskell.LSP.Types.WorkspaceSymbol where

import Data.Aeson.TH
import Data.Default
import Language.Haskell.LSP.Types.Common
import Language.Haskell.LSP.Types.DocumentSymbol
import Language.Haskell.LSP.Types.Progress
import Language.Haskell.LSP.Types.Utils

data WorkspaceSymbolKindClientCapabilities =
  WorkspaceSymbolKindClientCapabilities
   { -- | The symbol kind values the client supports. When this
     -- property exists the client also guarantees that it will
     -- handle values outside its set gracefully and falls back
     -- to a default value when unknown.
     --
     -- If this property is not present the client only supports
     -- the symbol kinds from `File` to `Array` as defined in
     -- the initial version of the protocol.
     _valueSet :: Maybe (List SymbolKind)
   } deriving (Show, Read, Eq)

deriveJSON lspOptions ''WorkspaceSymbolKindClientCapabilities

instance Default WorkspaceSymbolKindClientCapabilities where
  def = WorkspaceSymbolKindClientCapabilities (Just $ List allKinds)
    where allKinds = [ SkFile
                     , SkModule
                     , SkNamespace
                     , SkPackage
                     , SkClass
                     , SkMethod
                     , SkProperty
                     , SkField
                     , SkConstructor
                     , SkEnum
                     , SkInterface
                     , SkFunction
                     , SkVariable
                     , SkConstant
                     , SkString
                     , SkNumber
                     , SkBoolean
                     , SkArray
                     ]

data WorkspaceSymbolClientCapabilities =
  WorkspaceSymbolClientCapabilities
    { _dynamicRegistration :: Maybe Bool -- ^Symbol request supports dynamic
                                         -- registration.
    , _symbolKind :: Maybe WorkspaceSymbolKindClientCapabilities -- ^ Specific capabilities for the `SymbolKind`.
    } deriving (Show, Read, Eq)

deriveJSON lspOptions ''WorkspaceSymbolClientCapabilities

-- -------------------------------------

makeExtendingDatatype "WorkspaceSymbolOptions" [''WorkDoneProgressOptions] []
deriveJSON lspOptions ''WorkspaceSymbolOptions

makeExtendingDatatype "WorkspaceSymbolRegistrationOptions"
  [''WorkspaceSymbolOptions] []
deriveJSON lspOptions ''WorkspaceSymbolRegistrationOptions

-- -------------------------------------

makeExtendingDatatype "WorkspaceSymbolParams"
  [ ''WorkDoneProgressParams
  , ''PartialResultParams
  ]
  [("_query", [t| String |])]

deriveJSON lspOptions ''WorkspaceSymbolParams
