-- β-normal form

module Term.NormalForm where

open import Prelude
open import Term
open import Term.Weakening renaming (lookup to lookupR)
open import Term.Substitution
open import Term.Reduction
open import Term.Reduction.Properties

private
  variable
    Γ Δ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ
    ρ : Wk Γ Δ

mutual

  -- Neutrals

  data Ne : Term Γ a → Set where
    var : Ne (var x)
    app : Ne t → Nf u → Ne (app t u)

  -- Normal forms

  data Nf : Term Γ a → Set where
    ne  : Ne t → Nf t
    abs : Nf t → Nf (abs t)

-- Normal forms are closed under weakening.

mutual

  wk-Ne : (ρ : Wk Γ Δ) {t : Term Δ a} (u : Ne t) → Ne (wk ρ t)
  wk-Ne ρ var = var
  wk-Ne ρ (app u x) = app (wk-Ne ρ u) (wk-Nf ρ x)

  wk-Nf : (ρ : Wk Γ Δ) {t : Term Δ a} (u : Nf t) → Nf (wk ρ t)
  wk-Nf ρ (ne x) = ne (wk-Ne ρ x)
  wk-Nf ρ (abs n) = abs (wk-Nf (keep ρ) n)

-- Normal forms do indeed not reduce.

mutual
  noRedNe : Ne t → t ⟶ t' → ⊥
  noRedNe var ()
  noRedNe (app neu nf) (appl r) = noRedNe neu r
  noRedNe (app neu nf) (appr r) = noRedNf nf r

  noRedNf : Nf t → t ⟶ t' → ⊥
  noRedNf (ne neu) r = noRedNe neu r
  noRedNf (abs nf) (abs r) = noRedNf nf r
