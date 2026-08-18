-- "Weakening": transporting terms to larger contexts

module Term.Weakening where

open import Prelude
open import Term

private
  variable
    a b : Ty
    Γ Δ Φ : Context

-- ρ : Wk Γ Δ  transports a term living in context Δ to a larger context Γ.
-- The relative order of assumptions in Δ is preserved in Γ;
-- Γ is Δ with additional assumptions inserted anywhere.
--
-- In other words, Δ can be obtained by deleting some assumptions from Γ.
-- This perspective is taken by the constructor names, describing how Δ
-- is stepwise constructed from Γ, by either keeping or skipping assumptions.

data Wk : (Γ Δ : Context) → Set where
  done : Wk [] []
  skip : (ρ : Wk Γ Δ) → Wk (a ∷ Γ) Δ
  keep : (ρ : Wk Γ Δ) → Wk (a ∷ Γ) (a ∷ Δ)

-- If  Wk Γ Δ, then any assumption a ∈ Δ is also in Γ.
-- lookup (ρ : Wk Γ Δ) transport de Bruijn indices a ∈ Δ to those a ∈ Γ.
-- In particular, "skip" increases a de Bruijn index.

lookup : Wk Γ Δ → a ∈ Δ → a ∈ Γ
lookup (keep ρ) zero    = zero
lookup (keep ρ) (suc x) = suc (lookup ρ x)
lookup (skip ρ) x       = suc (lookup ρ x)

-- wk (ρ : Wk Γ Δ)  transports a term from context Δ to larger context Γ
-- by updating the de Bruijn indices.
-- In particular, it maps a term  t : Term Δ a  to a term  wk ρ t : Term Γ a.

wk : Wk Γ Δ → Term Δ a → Term Γ a
wk ρ (var x)   = var (lookup ρ x)
wk ρ (abs t)   = abs (wk (keep ρ) t)
wk ρ (app t u) = app (wk ρ t) (wk ρ u)

-- Weakening compose, so they form a category with identity idW.

idW : Wk Γ Γ
idW {Γ = []}    = done
idW {Γ = x ∷ Γ} = keep idW

-- We write composition in the diagrammatic order, so that
-- wk (compWW ρ ρ') = wk ρ ∘ wk ρ'.

compWW : Wk Γ Δ → Wk Δ Φ → Wk Γ Φ
compWW done     ρ'        = ρ'
compWW (skip ρ) ρ'        = skip (compWW ρ ρ')
compWW (keep ρ) (skip ρ') = skip (compWW ρ ρ')
compWW (keep ρ) (keep ρ') = keep (compWW ρ ρ')

-- Some shorthands for common weakenings and weakening operations.

skip1 : Wk (a ∷ Γ) Γ
skip1 = skip idW

skips : Wk Γ Δ → Wk (Φ ++ Γ) Δ
skips {Φ = []}    ρ = ρ
skips {Φ = a ∷ Φ} ρ = skip (skips ρ)

wk1 : Term Γ b → Term (a ∷ Γ) b
wk1 = wk skip1
