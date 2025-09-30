module Eval where

open import Prelude
open import Term

private
  variable
    a b : Ty
    Γ : Context

module Den (ξ : BaseTy → Set) where

  Value : Ty → Set
  Value (` α)   = ξ α
  Value (a ⇒ b) = Value a → Value b

  data Env : Context → Set where
    []  : Env []
    _∷_ : (v : Value a) (ρ : Env Γ) → Env (a ∷ Γ)

  lookup : Env Γ → a ∈ Γ → Value a
  lookup (v ∷ ρ) zero = v
  lookup (v ∷ ρ) (suc x) = lookup ρ x

  eval : Env Γ → Term Γ a → Value a
  eval ρ (var x)   = lookup ρ x
  eval ρ (abs t)   = λ v → eval (v ∷ ρ) t
  eval ρ (app t u) = eval ρ t (eval ρ u)
