-- Alternative proofs for generalizing idW to any ρ : Wk Γ Γ.

module Term.Weakening.Properties.Id where

open import Prelude
open import Term
open import Term.Weakening renaming (lookup to lookupW)
open import Term.Weakening.Properties using (Wk-cons)

open ≡-Reasoning

private
  variable
    a b : Ty
    Γ Δ Δ₁ Δ₂ Φ : Context
    x : a ∈ Γ
    t : Term Γ a
    ρ ρ' : Wk Γ Δ

-- These proofs of the same lemmata from Term.Weakening.Properties
-- need only Wk-cons, not (explicitly) the uniqueness of identity weakenings.

lookup-id : {ρ : Wk Γ Γ} → lookupW ρ x ≡ x
lookup-id {x = x}     {ρ = skip ρ} = case Wk-cons ρ of λ() -- impossible case
lookup-id {x = zero}  {ρ = keep ρ} = refl
lookup-id {x = suc x} {ρ = keep ρ} = cong suc lookup-id

wk-id : {ρ : Wk Γ Γ} → wk ρ t ≡ t
wk-id {t = var x} = cong var lookup-id
wk-id {t = abs t} = cong abs wk-id
wk-id {t = app t t₁} = cong₂ app wk-id wk-id

comp-W-id : {ρ' : Wk Γ Γ} → compWW ρ ρ' ≡ ρ
comp-W-id {ρ = done}   {ρ' = done}    = refl
comp-W-id {ρ = skip ρ} {ρ' = ρ'}      = cong skip comp-W-id
comp-W-id {ρ = keep ρ} {ρ' = skip ρ'} = case Wk-cons ρ' of λ()
comp-W-id {ρ = keep ρ} {ρ' = keep ρ'} = cong keep comp-W-id

comp-id-W : {ρ : Wk Γ Γ} → compWW ρ ρ' ≡ ρ'
comp-id-W {ρ' = ρ'}      {ρ = done}   = refl
comp-id-W {ρ' = ρ'}      {ρ = skip ρ} = case Wk-cons ρ of λ()
comp-id-W {ρ' = skip ρ'} {ρ = keep ρ} = cong skip comp-id-W
comp-id-W {ρ' = keep ρ'} {ρ = keep ρ} = cong keep comp-id-W
