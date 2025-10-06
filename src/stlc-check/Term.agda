-- Well-typed terms of the simply-typed lambda-calculus.

module Term where

open import Prelude
open import Exp public using (Ty; `_; _⇒_) renaming (Ident to BaseTy)

-- Typing contexts.

Context : Set
Context = List Ty

private
  variable
    a b : Ty
    Γ Δ : Context

-- De Bruijn indices: a variable points to a type in the context.

data _∈_ (a : Ty) : Context → Set where
  zero : a ∈ (a ∷ Γ)
  suc  : (x : a ∈ Γ) → a ∈ (b ∷ Γ)

-- Term Γ a contains only terms that have type a in context Γ.

data Term (Γ : Context) : Ty → Set where
  var : (x : a ∈ Γ) → Term Γ a
  abs : (t : Term (a ∷ Γ) b) → Term Γ (a ⇒ b)
  app : (t : Term Γ (a ⇒ b)) (u : Term Γ a) → Term Γ b
