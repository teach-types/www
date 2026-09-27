-- Well-typed terms of the simply-typed lambda-calculus.

module Term where

open import Prelude
open import Exp public using (Ty; BaseTy; `_; _⇒_)

-- Typing contexts.

data Context : Set where
  ε   : Context
  _∙_ : (Γ : Context) (a : Ty) → Context

private
  variable
    a b : Ty
    Γ Δ : Context

infixl 5 _∙_
infixl 4.5 _∙∙_

_∙∙_ : (Γ Δ : Context) → Context
Γ ∙∙ ε = Γ
Γ ∙∙ Δ ∙ a = (Γ ∙∙ Δ) ∙ a

-- De Bruijn indices: a variable points to a type in the context.

data _∈_ (a : Ty) : Context → Set where
  zero : a ∈ (Γ ∙ a)
  suc  : (x : a ∈ Γ) → a ∈ (Γ ∙ b)

-- Term Γ a contains only terms that have type a in context Γ.

data Term (Γ : Context) : Ty → Set where
  var : (x : a ∈ Γ) → Term Γ a
  abs : (t : Term (Γ ∙ a) b) → Term Γ (a ⇒ b)
  app : (t : Term Γ (a ⇒ b)) (u : Term Γ a) → Term Γ b
