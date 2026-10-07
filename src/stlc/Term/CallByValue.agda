-- Call-by-value reductions differs from call-by-name
-- by evaluating the argument before calling the function.
-- This is facilitated in a small-step semantics by restricting
-- the β rule to only fire when the argument is a value.
-- In pure simply-typed lambda-caluculus, values are λs or variables.

module Term.CallByValue where

open import Prelude
open import Prelude.Reduction
open import Term
open import Term.Substitution as Sub -- renaming (lookup to lookupS)
open import Term.Weakening

private
  variable
    Γ Δ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ

-- λs are the values of STLC.
-- When considering open terms, variables are also considered values.
-- The principle behind this: values are closed under substitution with values.

data Value : (t : Term Γ a) → Set where
  var : Value (var x)
  abs : Value (abs t)

-- A substition of values

data Values : (σ : Sub Γ Δ) → Set where
  ε   : Values (ε {Γ = Γ})
  _∙_ : (vs : Values σ) (v : Value t) → Values (σ ∙ t)

-- Values are closed under weakening

wkValue : (ρ : Wk Γ Δ) (v : Value t) → Value (wk ρ t)
wkValue ρ var = var
wkValue ρ abs = abs

wkValues : (ρ : Wk Γ Δ) (vs : Values σ) → Values (compWS ρ σ)
wkValues ρ ε = ε
wkValues ρ (vs ∙ v) = wkValues ρ vs ∙ wkValue ρ v

-- Values are closed under substitution with values.

lookupValue : (vs : Values σ) (x : a ∈ Γ) → Value (Sub.lookup σ x)
lookupValue (vs ∙ v) zero    = v
lookupValue (vs ∙ v) (suc x) = lookupValue vs x

subValue : (vs : Values σ) (v : Value t) → Value (sub σ t)
subValue vs var = lookupValue vs _
subValue vs abs = abs

-- Value substitutions are closed under composition

subValues : (vs : Values σ) (vs' : Values σ') → Values (compSS σ σ')
subValues vs ε = ε
subValues vs (vs' ∙ v) = subValues vs vs' ∙ subValue vs v

-- Call-by-value reduction

infix 4 _⟶ᵥ_

data _⟶ᵥ_ : (t t : Term Γ a) → Set where
  βᵥ    :  (v : Value u) → app (abs t) u ⟶ᵥ t [ u ]₀
  abs   :  (r : t ⟶ᵥ t') → abs t ⟶ᵥ abs t'
  appl  :  (r : t ⟶ᵥ t') → app t u ⟶ᵥ app t' u
  appr  :  (r : u ⟶ᵥ u') → app t u ⟶ᵥ app t u'

-- Multi-step call-by-value reduction

infix 4 _⟶ᵥ*_

_⟶ᵥ*_ : (t t' : Term Γ a) → Set
_⟶ᵥ*_ = Star _⟶ᵥ_

-- Weak-head equivalent of call-by-value reduction

infix 4 _⟶v_

data _⟶v_ : (t t : Term Γ a) → Set where
  βᵥ    :  (v : Value u) → app (abs t) u ⟶v t [ u ]₀
  appl  :  (r : t ⟶v t') → app t u ⟶v app t' u
  appr  :  (r : u ⟶v u') → app (abs t) u ⟶v app (abs t) u'

-- Multi-step weak call-by-value reduction

infix 4 _⟶v*_

_⟶v*_ : (t t' : Term Γ a) → Set
_⟶v*_ = Star _⟶v_
