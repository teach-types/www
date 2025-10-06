-- Haskell I/O as a RawMonad

module Prelude.IO where

open import Prelude
open import IO.Primitive.Core  public using (IO)

open import Effect.Functor     using (RawFunctor)
open import Effect.Applicative using (RawApplicative)

module IOFunctor where
  open import IO.Primitive.Core public using (_>>=_) renaming (pure to return)

  infixl 1 _>>_

  _>>_  : ∀ {b} {B : Set b} → IO ⊤ → IO B → IO B
  _>>_ = λ m m' → m >>= λ _ → m'

  infixr 1 _=<<_

  _=<<_  : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → IO A → IO B
  k =<< m = m >>= k

  -- The following definition is needed to create the RawFunctor instance.

  infixl 4 _<$>_

  _<$>_ :  ∀ {a b} {A : Set a} {B : Set b} → (A → B) → IO A → IO B
  f <$> m = m >>= λ a -> return (f a)

-- This module is needed to create the RawApplicative instance
-- in a way compatible with both std-lib v1.7.1/2 and v2.0.

module IOApplicative where
  open IOFunctor public

  rawFunctor : ∀{ℓ} → RawFunctor (IO {a = ℓ})
  rawFunctor = record { IOFunctor }

  pure : ∀{a} {A : Set a} → A → IO A
  pure = return

  infixl 4 _<*>_ _⊛_

  _<*>_ : ∀ {a b} {A : Set a} {B : Set b} → IO (A → B) → IO A → IO B
  mf <*> ma = mf >>= λ f → ma >>= λ a → return (f a)

  _⊛_ : ∀ {a b} {A : Set a} {B : Set b} → IO (A → B) → IO A → IO B
  _⊛_ = _<*>_

module IOMonad where
  open IOApplicative public

  -- Field rawApplicative is part of the RawMonad of std-lib v2.0
  -- Thus we have to construct the Applicative implementation
  -- even though we do not use it.
  --
  rawApplicative : ∀{ℓ} → RawApplicative (IO {a = ℓ})
  rawApplicative = record { IOApplicative }

{-# FOREIGN GHC import qualified Data.List #-}
{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.FilePath #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified System.Process #-}

-- Binding more Haskell functions

postulate
  exitFailure    : ∀{a} {A : Set a} → IO A
  getArgs        : IO (List String)
  putStrLn       : String → IO ⊤
  readFiniteFile : String → IO String
  takeBaseName   : String → String
  takeDirectory  : String → String
  writeFile      : String → String → IO ⊤
  callProcess    : String → List String → IO ⊤

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = map Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
{-# COMPILE GHC takeBaseName   = Data.Text.pack . System.FilePath.takeBaseName . Data.Text.unpack #-}
{-# COMPILE GHC takeDirectory  = Data.Text.pack . System.FilePath.takeDirectory . Data.Text.unpack #-}
{-# COMPILE GHC writeFile      = Data.Text.IO.writeFile . Data.Text.unpack #-}
{-# COMPILE GHC callProcess    = \ cmd -> System.Process.callProcess (Data.Text.unpack cmd) . Data.List.map Data.Text.unpack #-}
