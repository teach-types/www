module Prelude where

open import Agda.Primitive          public using () renaming (Set to Type)

open import Data.Bool.Base          public using (Bool; true; false; if_then_else_)
open import Data.Char.Base          public using (Char; isSpace)
open import Data.Empty              public using (⊥)
open import Data.Unit.Base          public using (⊤; tt)
open import Data.List.Base          public using (List; []; _∷_; [_]; _++_; concat; reverse; head) hiding (module List)
open import Data.List.NonEmpty.Base public using (List⁺; _∷_; _∷⁺_) hiding (module List⁺)
open import Data.Maybe.Base         public using (Maybe; nothing; just)
open import Data.Product.Base       public using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.String.Base        public using (String)
open import Data.Nat.Base           public using (ℕ; zero; suc) hiding (module ℕ)

open import Function                public using (id; _∘_; _$_; _|>_; case_of_; flip)

open import Relation.Binary.PropositionalEquality public using (_≡_; refl; sym; trans; subst; cong; cong₂; module ≡-Reasoning)
open import Relation.Nullary                      public using (Dec; yes; no)

module String where
  open Data.String.Base public using (_++_; concat; fromList; toList)
  open import Data.String public using (_≟_)

module List where
  open import Data.List.Base public using (map; foldl; foldr)

module List⁺ where
  open import Data.List.NonEmpty.Base public using (toList; foldr₁)

module All where
  open import Data.List.Relation.Unary.All public

module ℕ where
  open import Data.Nat.GeneralisedArithmetic public using (fold)
  open import Data.Nat.Show public using (show)
