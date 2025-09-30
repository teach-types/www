{-# OPTIONS --allow-unsolved-metas #-}

-- Bidirectional checker for the STLC.

module Check where

open import Prelude
open import Exp
open import Term

private
  variable
    a b : Ty
    Γ : Context

-- Errors thrown by the type checker.

data CheckError : Set where
  unboundIdentifier  : Ident → _
  applyNonFunction   : Ty → Exp → _
  inferUntypedLambda : _
  notSubtype         : (a b : Ty) → _

-- A scope maps identifiers to their type,
-- and indirectly to their de Bruijn index.

data Scope : Context → Set where
  empty : Scope []
  cons  : (x : Ident) (a : Ty) (sc : Scope Γ) → Scope (a ∷ Γ)

-- Looking up an identifier in the scope can fail.
-- If it succeeds, it returns the type and evidence that
-- this type is in the context.
-- This evidence is the de Bruijn index.

lookupIdent : Scope Γ → Ident → Maybe (∃ λ a → a ∈ Γ)
lookupIdent empty x = nothing
lookupIdent (cons y a sc) x =
  case y String.≟ x of λ where
    (yes _) → just (a , zero)
    (no  _) → case lookupIdent sc x of λ where
      (just (a , x)) → just (a , suc x)
      nothing → nothing

-- The result of inferring an expression in a context,
-- if inference succeeds,
-- is its type and translation to a well-typed term.

data Infer (Γ : Context) : Set where
  inferred : (a : Ty) (t : Term Γ a) → _
  failed   : (err : CheckError) → _

-- The result of checking an expression against a type in a context,
-- if checking succeeds,
-- is its translation to a well-typed term.

data Check (Γ : Context) (a : Ty) : Set where
  checked : (t : Term Γ a) → _
  failed  : (err : CheckError) → _

-- The bidirectional checker.

mutual

  -- Infer the type of an expression.  Γ ⊢ e ⇉ ?

  infer : Scope Γ → Exp → Infer Γ

  -- Case: Γ ⊢ x ⇉ ?.
  infer sc (var x) = {!!}

  -- Case: Γ ⊢ f e ⇉ ?.
  infer sc (app f e) = {!!}

  -- Case Γ ⊢ (λ x → e) ⇉ ?.  Fail.
  infer sc (abs (uBind x) e) = failed inferUntypedLambda

  -- Case Γ ⊢ (λ (x : a) → e) ⇉ ?.
  infer sc (abs (tBind x a) e) = {!!}

  -- Check an expression against a type.  Γ ⊢ e ⇇ a

  check : Scope Γ → Exp → (a : Ty) → Check Γ a

  -- Case: Γ ⊢ λ x → e ⇇ a ⇒ c.
  check sc (abs (uBind x) e) (a ⇒ c) = {!!}

  -- Otherwise: try to infer.  Γ ⊢ e ⇉ b
  check sc e a = {!!}
