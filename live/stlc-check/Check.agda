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
      (just (a , i)) → just (a , suc i)
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
  infer sc (var x) = case lookupIdent sc x of λ where
    (just (a , i)) → inferred a (var i)
    nothing → failed (unboundIdentifier x)

  -- Case: Γ ⊢ f e ⇉ ?.

  -- Variant with "with".  Desugars into local functions
  -- infer sc (app f e) with infer sc f
  -- ... | failed err = failed err
  -- ... | inferred (` α) t = failed (applyNonFunction (` α) e)
  -- ... | inferred (a ⇒ b) t with check sc e a
  -- ... | checked u = inferred _ (app t u)
  -- ... | failed err = failed err

  -- -- Variant with local functions (most basic).
  -- infer {Γ = Γ} sc (app f e) = infer-with (infer sc f)
  --   where
  --   infer-with : (r : Infer Γ) → Infer Γ
  --   infer-with (inferred (a ⇒ b) t) = infer-with2 (check sc e a)
  --     where
  --     infer-with2 : Check Γ a → Infer Γ
  --     infer-with2 (checked u) = inferred _ (app t u)
  --     infer-with2 (failed err) = failed err
  --   infer-with (failed err) = failed err
  --   infer-with (inferred (` α) t) = failed (applyNonFunction (` α) e)

  -- Variant with "λ where" and "case_of_".
  infer sc (app f e) = case infer sc f of λ where
    (inferred (` α) t) → failed (applyNonFunction (` α) e)
    (inferred (a ⇒ b) t) → case check sc e a of λ where
       (checked u) → inferred b (app t u)
       (failed err) → failed err
    (failed err) → failed err

  -- Case Γ ⊢ (λ x → e) ⇉ ?.  Fail.
  infer sc (abs (uBind x) e) = failed inferUntypedLambda

  -- Case Γ ⊢ (λ (x : a) → e) ⇉ ?.
  infer sc (abs (tBind x a) e) = case infer (cons x a sc) e of λ where
    (inferred b t) → inferred (a ⇒ b) (abs t)
    (failed err) → failed err

  -- Check an expression against a type.  Γ ⊢ e ⇇ a

  check : Scope Γ → Exp → (a : Ty) → Check Γ a

  -- Case: Γ ⊢ λ x → e ⇇ a ⇒ c.
  check sc (abs (uBind x) e) (a ⇒ c) = case check (cons x a sc) e c of λ where
     (checked t) → checked (abs t)
     (failed err) → failed err

  -- Otherwise: try to infer.  Γ ⊢ e ⇉ b
  check {Γ = Γ} sc e a = case infer sc e of λ where
     (inferred b t) → case b == a of λ where
       (false , _) → failed (notSubtype b a)
       -- (true  , p) → checked (subst (Term Γ) {x = b} {y = a} p t)
       (true  , refl) → checked t
     (failed err) → failed err
    where
      _==_ : (a b : Ty) → Σ Bool λ x → if x then a ≡ b else ⊤
      (` α) == (` β) = case α String.≟ β of λ where
        -- (yes p) → true , cong (`_) p
        (yes refl) → true , refl
        (no ¬p) → false , _
      (` α) == (b ⇒ b₁) = false , _
      (a ⇒ a₁) == (` α) = false , _
      (a ⇒ a₁) == (b ⇒ b₁) = case a == b of λ where
        (false , _) → false , _
        (true , p) → case a₁ == b₁ of λ where
          (false , _) → false , _
          (true , q) → true , cong₂ _⇒_ p q
