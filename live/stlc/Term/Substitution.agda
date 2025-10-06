-- For computing with terms, in particular, for β-reduction, we need
-- to substitute terms for variables.
--
-- Given  t : Term (a ∷ Γ) b  and  u : Term Γ a  we wish to define substitution
-- for de Bruijn index zero : a ∈ (a ∷ Γ), namely  t [ u ]₀ : Term Γ b.
-- This then allows us to define β-reduction  app (abs t) u ⟶ t [ u ]₀.
-- (Observe that  abs t : Term Γ (a ⇒ b).)
--
-- However, substitution for index 0 cannot be defined directly, because
-- (abs t) [ u ]₀  will require to replace index 1 in t by u.
-- Moreover, abs (t [ u ]₁) would not be correct yet since u's own index 0
-- would be captured by "abs" while it is supposed to be a free index.
-- We need thus to increase all indices in u by 1, correct would then be
-- abs (t [ lift u ]₁) where "lift" does the increment.
--
-- Increasing de Bruijn indices could also be implemented by substitution,
-- but then we would need a substitution that can replace all indices
-- rather than just a particular one.
-- This is often called "simultaneous substitution or parallel substitution".
--
-- We will take this concept as our primitive and write σ : Sub Γ Δ for
-- a (parallel) substitution which replaces each index x : a ∈ Δ by a term
-- t : Term Γ a, so we get the substitution operation
--
--     sub : (σ : Sub Γ Δ) (t : Term Δ a) → Term Γ a .
--
-- In the case of abstraction, we get
--
--     sub (σ : Sub Γ Δ) (abs t : Term Δ (a ⇒ b)) : Term Γ (a ⇒ b)
--       = abs (sub (lift σ : Sub (a ∷ Γ) (a ∷ Δ))
--                  (t      : Term (a ∷ Δ) b))
--
-- The idea is that  lift σ  replaces index 0 by itself and index x+1 by
-- σ(x) where each index in σ(x) is incremented.
--
-- We take the simplest idea of representing substitutions as just a list
-- of terms where each term in the list is the replacement for one de Bruijn index.
--
--    []      : Sub Γ []       (no indices to replace)
--
--    (t ∷ σ) : Sub Γ (a ∷ Δ)  when  t : Term Γ a  and  σ : Sub Γ Δ.
--
-- In the second rule, t is the replacement for index 0 and σ the one for the other indices.
--
-- Substitution can be composed by applying a substitution to each term of the other substitution:
--
--     compSS : Sub Γ Δ → Sub Δ Φ → Sub Γ Φ
--     compSS σ [] = []
--     compSS σ (t ∷ σ') = sub σ t ∷ compSS σ σ'
--
-- The substitution
--
--    skip1 : Sub (a ∷ Γ) Γ
--    skip1 = var 1 ∷ var 2 ∷ ... ∷ var |Γ| ∷ []
--
-- would do the job of incrementing each index by 1.
-- Thus, we could define
--
--    lift   : Sub Γ Δ → Sub (a ∷ Γ) (a ∷ Δ)
--    lift σ = var zero ∷ compSS skip1 σ
--
-- and use lift in the definition of sub for abstraction (see above).
--
-- Unfortunately, such a definition would be rejected by Agda's termination checker.
-- We are defining sub, lift, compSS by mutual recursion and termination is not obvious.
-- To see why the definitions are well-founded, we need to observe that skip1 is
-- a "variable substitution" and so "compSS skip1 σ" does not morally increase the
-- size of the substitution σ.  With some indexing tricks we could make this work.
--
-- However, we take a more conservative approach and define "variable substitutions"
-- completely separately, in a restricted form called "weakenings" (module Term.Weakenings),
-- Wk Γ Δ.  These can be turned into substitutions with fromWk : Wk Γ Δ → Sub Γ Δ.
-- They allow us to define "lift" before "sub" breaking the cycle.

module Term.Substitution where

open import Prelude
open import Term
open import Term.Weakening using (Wk; done; keep; skip; skip1; wk; idW; compWW) renaming (lookup to lookupR)

private
  variable
    a b : Ty
    Γ Δ Φ : Context

-- "Parallel" / "simulatenous" substitutions Sub Γ Δ
-- are lists of terms living in Γ,
-- one for each variable bound in Δ.

data Sub : (Γ Δ : Context) → Set where
  []   : Sub Γ []
  _∷_  : (t : Term Γ a) (σ : Sub Γ Δ) → Sub Γ (a ∷ Δ)

-- compWS ρ σ weakens substitution σ according to ρ,
-- i.e., applies the weakening ρ to each term in σ.

compWS : Wk Γ Δ → Sub Δ Φ → Sub Γ Φ
compWS ρ [] = []
compWS ρ (t ∷ σ) = wk ρ t ∷ compWS ρ σ

-- We introduce a shorthand "weak σ" to weaken a substitution σ
-- by just one new variable.

weak : Sub Γ Δ → Sub (a ∷ Γ) Δ
weak = compWS skip1

-- "lift σ" lifts substitution σ under a binder such as "abs".
-- The de Bruijn index 0 bound here is mapped to itself,
-- all other de Bruijn indices are incremented.

lift : Sub Γ Δ → Sub (a ∷ Γ) (a ∷ Δ)
lift σ = var zero ∷ weak σ

-- "lookup σ x" returns the term t : Term Γ a
-- the variable x : a ∈ Δ is mapped to by substitution σ : Sub Γ Δ.
-- In other worss, "lookup σ" interprets σ as function
-- from indices to terms.

lookup : Sub Γ Δ → a ∈ Δ → Term Γ a
lookup [] ()
lookup (t ∷ σ) zero = t
lookup (t ∷ σ) (suc x) = lookup σ x

-- "sub σ t" carries out the substitution σ in term t.
-- So, "sub σ" interprets σ as function from terms to terms.

sub : Sub Γ Δ → Term Δ a → Term Γ a
sub σ (var x)   = lookup σ x
sub σ (abs t)   = abs (sub (lift σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)

-- Weakenings can be seen as special substitutions ("variable substitutions").

fromWk : (ρ : Wk Γ Δ) → Sub Γ Δ
fromWk done     = []
fromWk (skip ρ) = weak (fromWk ρ)
fromWk (keep ρ) = lift (fromWk ρ)

-- Substitutions Sub Γ Δ form a category where contexts are the objects
-- and substitutions the morphisms.

idS : Sub Γ Γ
idS = fromWk idW

compSS : Sub Γ Δ → Sub Δ Φ → Sub Γ Φ
compSS σ [] = []
compSS σ (t ∷ τ) = sub σ t ∷ compSS σ τ

-- The singleton substitution is the substitution we are mainly interested in.

sg : Term Γ a → Sub Γ (a ∷ Γ)
sg t = t ∷ idS

-- Substituting a term for de Bruijn index 0.

infixr 10 _[_]₀

_[_]₀ : Term (a ∷ Γ) b → Term Γ a → Term Γ b
t [ u ]₀ = sub (sg u) t

-- We can restrict a substitution σ : Sub Γ Δ
-- by a weakening ρ : Wk Δ Φ that selects
-- some terms from the list σ.
-- This gives the restricted substitution compSW σ ρ : Sub Γ Φ
-- that only substitutes for the variables in Φ (sublist of Δ).

compSW : Sub Γ Δ → Wk Δ Φ → Sub Γ Φ
compSW []       done    = []
compSW (t ∷ σ) (skip ρ) = compSW σ ρ
compSW (t ∷ σ) (keep ρ) = t ∷ compSW σ ρ
