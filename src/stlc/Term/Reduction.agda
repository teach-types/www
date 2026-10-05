-- Single step reduction

module Term.Reduction where

open import Prelude
open import Prelude.Reduction
open import Term
open import Term.Substitution

private
  variable
    Γ Δ : Context
    a : Ty
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ

-- Full one-step reduction

infix 1 _⟶_

data _⟶_ : (t t' : Term Γ a) → Set where
  β    : app (abs t) u ⟶ t [ u ]₀
  appl : (r : t ⟶ t') → app t u ⟶ app t' u
  appr : (r : u ⟶ u') → app t u ⟶ app t u'
  abs  : (r : t ⟶ t') → abs t ⟶ abs t'

-- Full reduction

_⟶*_ : (t t' : Term Γ a) → Set
_⟶*_ = Star _⟶_

-- data _⟶*_ : (t t' : Term Γ a) → Set where
--   []  : t ⟶* t
--   _∷_ : (r : t ⟶ t') (rs : t' ⟶* t'') → t ⟶* t''

-- Full reduction as snoc-list

data _⟶*ˢ_ : (t t' : Term Γ a) → Set where
  []  : t ⟶*ˢ t
  _▷_ : (rs : t ⟶*ˢ t') (r : t' ⟶ t'') → t ⟶*ˢ t''

consˢ : t ⟶ t' → t' ⟶*ˢ t'' → t ⟶*ˢ t''
consˢ r [] = [] ▷ r
consˢ r (rs ▷ r') = consˢ r rs ▷ r'

reverse* : t ⟶* t' → t ⟶*ˢ t'
reverse* [] = []
reverse* (r ∷ rs) = consˢ r (reverse* rs)

-- Full reduction of substitutions

data _⟶*S_ : (σ σ' : Sub Γ Δ) → Set where
  ε  : (ε {Γ = Γ}) ⟶*S ε
  _∙_ :  (rσ : σ ⟶*S σ') (rs : t ⟶* t') → (σ ∙ t) ⟶*S (σ' ∙ t')

-- One step weak head reduction

infix 1 _⟶w_

data _⟶w_ : (t t' : Term Γ a) → Set where
  β    : app (abs t) u ⟶w t [ u ]₀
  appl : (w : t ⟶w t') → app t u ⟶w app t' u

-- Multi-step weak head reduction

_⟶w*_ : (t t' : Term Γ a) → Set
_⟶w*_ = Star _⟶w_

-- Weak head reduction is a reduction

unfoldW : t ⟶w t' → t ⟶ t'
unfoldW β = β
unfoldW (appl r) = appl (unfoldW r)
