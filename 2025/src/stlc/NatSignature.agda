-- Free variables "zero : ℕ" and "suc : ℕ → ℕ"

module NatSignature where

open import Prelude
open import Term
open import Check using (Scope; empty; cons)
import Eval

-- Signature for natural numbers

pattern tℕ = ` "ℕ"
pattern tℕ⇒ℕ = tℕ ⇒ tℕ
pattern Chℕ  = tℕ⇒ℕ ⇒ tℕ⇒ℕ

-- Context and scope for "zero : ℕ, suc : ℕ → ℕ"

Γℕ : Context
Γℕ = tℕ⇒ℕ ∷ tℕ ∷ []

scopeℕ : Scope Γℕ
scopeℕ = cons "suc" tℕ⇒ℕ (cons "zero" tℕ empty)

-- Evaluation of natural number terms

-- For simplicity, all base types are interpreted as ℕ

ξℕ : BaseTy → Set
ξℕ _ = ℕ

open Eval.Den ξℕ using (Env; []; _∷_; eval)

-- The free variables "zero" and "suc" are interpreted as the respective constructors of the natural numbers.

ρℕ : Env Γℕ
ρℕ = suc ∷ zero ∷ []

-- Evaluating a term of type ℕ with free variables "zero" and "suc".

evalℕ : Term Γℕ tℕ → ℕ
evalℕ = eval ρℕ
