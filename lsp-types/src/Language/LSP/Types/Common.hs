{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE TypeApplications           #-}

-- | Common types that aren't in the specification
module Language.LSP.Types.Common where

import Control.Applicative
import Control.DeepSeq
import Data.Aeson
import GHC.Generics
import Data.Kind

data Union (as :: [Type]) where
  This :: !a          -> Union (a ': as)
  That :: !(Union as) -> Union (a ': as)

absurdUnion :: Union '[] -> a
absurdUnion = \case{}

class UnionCase (xs :: [Type]) where
  type CaseAnalyse xs (r :: Type) :: Type
  unionCase :: Union xs -> CaseAnalyse xs r
  liftRes :: r -> CaseAnalyse xs r

instance UnionCase '[] where
  type CaseAnalyse '[] r = r
  unionCase = absurdUnion
  liftRes = id

instance UnionCase xs => UnionCase (x ': xs) where
  type CaseAnalyse (x ': xs) r = (x -> r) -> CaseAnalyse xs r

  unionCase :: forall r. Union (x ': xs) -> (x -> r) -> CaseAnalyse xs r
  unionCase (This x) f = liftRes @xs (f x)
  unionCase (That y) _ = unionCase @_ @r y

  liftRes r = const (liftRes @xs r)

instance Eq (Union '[]) where
  (==) = absurdUnion
deriving instance (Eq a , Eq (Union as)) => Eq (Union (a ': as))

instance Ord (Union '[]) where
  compare = absurdUnion
deriving instance (Ord a , Ord (Union as)) => Ord (Union (a ': as))

instance Read (Union '[]) where
  readsPrec _ = mempty
deriving instance (Read a , Read (Union as)) => Read (Union (a ': as))

instance ToJSON (Union '[]) where
  toJSON = absurdUnion
instance (ToJSON a, ToJSON (Union as)) => ToJSON (Union (a ': as)) where
  toJSON (This x) = toJSON x
  toJSON (That x) = toJSON x

instance FromJSON (Union '[]) where
  parseJSON _ = mempty
instance (FromJSON a, FromJSON (Union as)) => FromJSON (Union (a ': as)) where
  -- Important: Try to parse the **rightmost** type first, as in the specification
  -- the more complex types tend to appear on the right of the |, i.e.
  -- @colorProvider?: boolean | DocumentColorOptions | DocumentColorRegistrationOptions;@
  parseJSON v = That <$> parseJSON v <|> This <$> parseJSON v

instance Show (Union '[]) where
  showsPrec _ = absurdUnion
deriving instance (Show a , Show (Union as)) => Show (Union (a ': as))

instance NFData (Union '[]) where
  rnf = absurdUnion
instance (NFData a , NFData (Union as)) => NFData (Union (a ': as)) where
  rnf (This x) = rnf x
  rnf (That x) = rnf x

type family Delete (r :: k) (rs :: [k]) :: [k] where
  Delete r (r ': rs) = rs
  Delete r (s ': rs) = s ': Delete r rs

-- | Delete all the elements of the first list from the second
type family DeleteL (as :: [k]) (bs :: [k]) :: [k] where
  DeleteL '[] xs       = xs
  DeleteL (x ': xs) ys = DeleteL xs (Delete x ys)

type family (++) (as :: [k]) (bs :: [k]) :: [k] where
  (++) '[] xs       = xs
  (++) (x ': xs) ys = x ': (xs ++ ys)

class bs ~ Delete a as => UElem (a :: Type) (as :: [Type]) (bs :: [Type]) where
  ulift  :: a -> Union as
  ulift = upromote . Right
  umatch :: Union as -> Either (Union bs) a
  upromote :: Either (Union bs) a -> Union as

instance {-# OVERLAPPING #-} UElem a (a ': as) as where
  umatch (This a) = Right a
  umatch (That b) = Left b
  upromote (Left x) = That x
  upromote (Right x)  = This x

instance {-# OVERLAPPABLE #-} (UElem a as bs, Delete a (b ': as) ~ cs, cs ~ (b ': bs)) => UElem a (b ': as) cs where
  umatch (This a) = Left $ ulift a
  umatch (That b) = case umatch b of
    Right x -> Right x
    Left y -> Left $ That y
  upromote (Left (This b)) = This b
  upromote (Left (That bs)) = That $ upromote (Left bs :: Either (Union bs) a)
  upromote (Right x) = That (ulift x)

class cs ~ DeleteL as bs => USubset (as :: [Type]) (bs :: [Type]) (cs :: [Type]) where
  urelax :: Union as -> Union bs
  urestrict :: Union bs -> Either (Union cs) (Union as)

instance USubset '[] bs bs where
  urelax = absurdUnion
  urestrict = Left

instance (UElem a bs bsMa, USubset as bsMa cs) => USubset (a ': as) bs cs where
  urelax (This a) = ulift a
  urelax (That b) = upromote $ (Left @_ @a (urelax b))

  urestrict bs = case umatch bs of
    Right a  -> Right (This a)
    Left ds -> case urestrict ds of
      Left  cs -> Left cs
      Right as -> Right (That as)

-- | A terser, isomorphic data type for 'Either', that does not get tagged when
-- converting to and from JSON.
type family (|?) (a :: Type) (b :: Type) :: Type where
  (|?) (Union xs) (Union ys) = Union (xs ++ ys)
  (|?) (Union xs) x = Union (xs ++ '[x])
  (|?) x (Union xs) = Union (x ': xs)
  (|?) x y = Union '[x,y]
infixr |?

-- | All LSP types representing a list **must** use this type rather than '[]'.
-- In particular this is necessary to change the 'FromJSON' instance to be compatible
-- with Elisp (where empty lists show up as 'null')
newtype List a = List [a]
                deriving (Show,Read,Eq,Ord,Semigroup,Monoid,Functor,Foldable,Traversable,Generic)

instance NFData a => NFData (List a)

instance (ToJSON a) => ToJSON (List a) where
  toJSON (List ls) = toJSON ls

instance (FromJSON a) => FromJSON (List a) where
  parseJSON Null = return (List [])
  parseJSON v      = List <$> parseJSON v

data Empty = Empty deriving (Eq,Ord,Show)
instance ToJSON Empty where
  toJSON Empty = Null
instance FromJSON Empty where
  parseJSON Null = pure Empty
  parseJSON _ = mempty
