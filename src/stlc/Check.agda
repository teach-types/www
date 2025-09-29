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
  tooManyArguments   : Ty → List Exp → _
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

  -- Case: Γ ⊢ x e1...en ⇉ ?.
  infer sc (ne x es) =
    case lookupIdent sc x of λ where
      nothing → failed (unboundIdentifier x)
      -- Infer Γ | x : Γ(x) ⊢ e1...en ⇉ ?
      (just (a , y)) → inferSpine sc a (Term.var y) es

  -- Case Γ ⊢ (λ x → e) e1...en ⇉ ?.  Fail.
  infer sc (abs (uBind x) e es) = failed inferUntypedLambda

  -- Case Γ ⊢ (λ (x : a) → e) e1...en ⇉ ?.
  infer sc (abs (tBind x a) e es) =
    -- Infer Γ, x:a ⊢ e ⇉ b.
    case infer (cons x a sc) e of λ where
      -- Infer Γ | λ x → t : a ⇒ b ⊢ e1...en ⇉ ?
      (inferred b t) → inferSpine sc (a ⇒ b) (abs t) es
      (failed err) → failed err

  -- Infer the types of the arguments.  Γ | t : a ⊢ e1...en ⇉ ?

  inferSpine : Scope Γ → (a : Ty) → Term Γ a → List Exp → Infer Γ

  -- Case: no arguments (left): Done!   Γ | t : a ⊢ ε ⇉ a
  inferSpine sc a t [] = inferred a t

  -- Case: no function type: Fail.
  inferSpine sc (` α) t (e ∷ es) = failed (tooManyArguments (` α) (e ∷ es))

  -- Case: function type Γ | t : a ⇒ b ⊢ e e1...en ⇉ ?
  inferSpine sc (a ⇒ b) t (e ∷ es) =
    -- Check Γ ⊢ e ⇇ a.
    case check sc e a of λ where
      -- Infer Γ | t u : b ⊢ e1...en ⇉ ?
      (checked u)  → inferSpine sc b (app t u) es
      (failed err) → failed err

  -- Check an expression against a type.  Γ ⊢ e ⇇ a

  check : Scope Γ → Exp → (a : Ty) → Check Γ a

  -- Case: Γ ⊢ λ x → e ⇇ a ⇒ c.
  check sc (lam (uBind x) e) (a ⇒ c) =
    -- Check Γ, x:a ⊢ e ⇇ c.
    case check (cons x a sc) e c of λ where
      (checked t) → checked (abs t)
      (failed err) → failed err

  -- Otherwise: try to infer.  Γ ⊢ e ⇉ b
  check sc e a =
    case infer sc e of λ where
      (inferred b u) →
         -- Compare given and inferred type.
         case eqType b a of λ where
           (yes refl) → checked u
           (no _) → failed (notSubtype b a)
      (failed err) → failed err
