module Prelude.Reduction where

open import Prelude
open import Relation.Binary.Construct.Closure.ReflexiveTransitive public
  using (Star) hiding (module Star) renaming (ε to []; _◅_ to _∷_)
open import Relation.Binary.Rewriting public using (Confluent)

module Star where
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive public

private
  variable
    A : Type
    a b c d : A

Rel : Type → Type₁
Rel A = A → A → Type

_⊂_ : (R S : Rel A) → Type
_⊂_ {A = A} R S = ∀{a b : A} → R a b → S a b

module _ (R : Rel A) where

  Joinable : Rel A
  Joinable a₁ a₂ = ∃ λ b → R a₁ b × R a₂ b

  Diamond : Type
  Diamond = ∀{a a₁ a₂} → R a a₁ → R a a₂ → Joinable a₁ a₂

  module _ (dia : Diamond) where

    -- Strip lemma

    strip : R a b → Star R a c → ∃ λ d → Star R b d × R c d
    strip {b = b} r [] = b , [] , r
    strip r₁ (r₂ ∷ rs) with dia r₁ r₂
    ... | c , r₂' , r₁' with strip r₁' rs
    ... | d , rs' , r₁'' = d , r₂' ∷ rs' , r₁''

    confluent : Confluent R
    confluent [] rs₂ = _ , rs₂ , []
    confluent (r ∷ rs₁) rs₂ with strip r rs₂
    ... | _ , rs₂' , r' with confluent rs₁ rs₂'
    ... | _ , rs₃ , rs₄ = _ , rs₃ , r' ∷ rs₄


module _ {R S : Rel A} (R⊂S : R ⊂ S) (S⊂R* : S ⊂ Star R) (dia : Diamond S) where

  private
    R*⊂S* : Star R ⊂ Star S
    R*⊂S* = Star.map R⊂S

    S*⊂R* : Star S ⊂ Star R
    S*⊂R* = S⊂R* Star.⋆

  sandwich : Confluent R
  sandwich rs rs' with confluent S dia (R*⊂S* rs) (R*⊂S* rs')
  ... | _ , ss , ss' = _ , S*⊂R* ss , S*⊂R* ss'
