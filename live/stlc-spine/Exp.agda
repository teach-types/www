-- Abstract syntax of expressions as produced by the parser.

module Exp where

open import Prelude

-- Simple types.

BaseTy = String

data Ty : Type where
  `_   : (α : BaseTy) → Ty
  _⇒_  : (t₁ t₂ : Ty) → Ty

infixr 10 `_
infixr  9 _⇒_

-- Typed and untyped binding.

Ident = String

data Bind : Type where
  uBind : (x : Ident) → Bind
  tBind : (x : Ident) (t : Ty) → Bind

-- Expressions in spine form.
-- Applications are gathered.

data Exp : Type where
  ne  : (x : Ident)          (es : List Exp) → Exp   -- "neutral"     x e1 ... en
  abs : (b : Bind) (e : Exp) (es : List Exp) → Exp   -- "abstraction" (λ x → e) e1 ... en

pattern var x = ne x []
pattern lam b e = abs b e []

-- Smart constructor for expressions.

apps : Exp → List Exp → Exp
apps (ne  x   es) es' = ne  x (es ++ es')
apps (abs b e es) es' = abs b e (es ++ es')

-- Reassociate types (for parsing).

mkTy : Ty → List Ty → Ty
mkTy a [] = a
mkTy a (b ∷ bs) = mkTy (a ⇒ b) bs

-- Deciding type equality.

-- Injectivity of constructors.

inj` : ∀{α β} → (` α) ≡ (` β) → α ≡ β
inj` refl = refl

inj⇒l : ∀{a b c d : Ty} → (a ⇒ b) ≡ (c ⇒ d) → a ≡ c
inj⇒l refl = refl

inj⇒r : ∀{a b c d : Ty} → (a ⇒ b) ≡ (c ⇒ d) → b ≡ d
inj⇒r refl = refl

-- discr-l : ∀{α b c} → (` α) ≡ (b ⇒ c) → ⊥
-- discr-l ()

eqType : (a b : Ty) → Dec (a ≡ b)

-- Case: both type constants

eqType (` α) (` β) =
  case α String.≟ β of λ where
    (yes refl) → yes refl
    (no p)     → no λ q → p (inj` q)

-- Case: both function types

eqType (a ⇒ a₁) (b ⇒ b₁) =
  case eqType a b of λ where
    (yes refl) →
      case eqType a₁ b₁ of λ where
        (yes refl) → yes refl
        (no p)     → no λ q → p (inj⇒r q)
    (no p)         → no λ q → p (inj⇒l q)

-- Cases for different constructors

eqType (` α) (b ⇒ b₁) = no λ()
eqType (a ⇒ a₁) (` α) = no λ()
