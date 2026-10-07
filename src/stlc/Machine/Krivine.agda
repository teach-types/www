-- Call-by-name abstract machine (Jean-Louis Krivine 1980s)
-- ========================================================
--
-- Machines allow us to evaluate λ-terms much more efficiently
-- than via big-step semantics or small-step semantics.
--
-- Big-step semantics, aka, interpreters, are not terrible,
-- but, being non-tail-recursive functions,
-- have the overhead of the call-stacks of the programming
-- language they are implemented in.
--
-- Small-step semantics, implemented directly, is terrible
-- from a performance point.
-- First, each step searches for a redex from scratch,
-- e.g. if we have (λxt) u₀ u₁ ... uₙ, we have to
-- traverse through a sequence of applications uₙ ... u₁
-- until we locate the redex (λxt) u₀, and reduction
-- gives us t[u₀/x] u₁ ... uₙ which again requires us
-- to traverse the application chain to get to the point
-- of interest.
--
-- Machines save the work of locating the redex
-- using a "zipper"-like technique (Huet, 1997)
-- decomposing e.g. (λxt) u₀ u₁ ... uₙ into a head
-- ("control") λxt and a stack u₀ ∷ u₁ ∷ ... uₙ ∷ []
-- of arguments that still need to be applied.
-- Reduction then just pops off the top of the stack
-- and leaves us with control t[u₀/x] and stack u₁ ∷ ... uₙ ∷ [].
--
-- The second improvement is that machines do not carry out
-- the substitution t[u₀/x] eagerly but propagate it step
-- by step through t so that it is resolved as late as possible,
-- just when needed.
-- This lazy handling of substitution allows also to fuse subsequent
-- substitutions into a single traversal rather than doing one
-- per substitution.
--
-- The Krivine machine can be considered the simplest of the machines
-- optimizing redex location and substitution.
-- It is based on the concept of a closure k ::= ⟨t,ρ⟩ which pairs a term
-- with a substitution ρ that still has to be applied to the term.
-- However ρ is not mapping variables to terms, but in turn to
-- closures.
-- A state q of the Krivine machine is a non-empty list of closures,
-- where the head of this list being worked on and the tail of the list
-- is the stack (sometimes called continuation).
-- The machine is described as a set of state transitions, with just
-- 3 rules, one per form of control: variable, application, abstraction.
--
-- Variable (VAR):
--   ⟨x, ρ⟩ ∷ s        ⟶  ρ(x) ∷ s
--
-- Application (APP):
--   ⟨t u, ρ⟩ ∷ s      ⟶  ⟨t, ρ⟩ ∷ ⟨u, ρ⟩ ∷ s
--
-- Abstraction (ABS):
--   ⟨λxt, ρ⟩ ∷ k ∷ s  ⟶  ⟨t, ρ.k/x⟩ ∷ s
--
-- The variable and application rules just implement the propagation
-- rules for substitutions:
--
--   x    [σ] = σ(x)
--   (t u)[σ] = t[σ] u[σ]
--
-- However, substitutions do not propagate into abstractions.
-- Instead, we perform a "function call" by picking the top closure k
-- from the stack and assigning it to the function parameter x.
-- This is facilitated by extending the environment ρ by the binding k/x
-- ("k for x").
--
-- The initial state ⌜t⌝ of the Krivine machine for evaluating a closed term t
-- is ⟨t, ε⟩ ∷ [], thus, t in the empty environment on the empty stack.
-- The stack will then be populated by traversing the applications in t
-- until we hit the λ in the head (cannot be a variable because t is closed).
-- This will perform the first call, with the first binding entering the environment.
-- The body of the λ will then be evaluated in this environment under the stack
-- we have constructed, etc.
--
-- Here is a example run of the SKII term, given as a list of subsequent states.
--
--       ⟨ (λxλyλz.(xz)(yz)) (λaλb.a) (λc.c) (λd.d), ε ⟩ ∷ []
--   ⟶ ⟨ (λxλyλz.(xz)(yz)) (λaλb.a) (λc.c), ε ⟩ ∷ ⟨ λd.d, ε ⟩ ∷ []
--   ⟶ ⟨ (λxλyλz.(xz)(yz)) (λaλb.a), ε ⟩ ∷ ⟨ λc.c, ε ⟩ ∷ ⟨ λd.d, ε ⟩ ∷ []
--   ⟶ ⟨ λxλyλz.(xz)(yz), ε ⟩ ∷ ⟨ λaλb.a, ε ⟩ ∷ ⟨ λc.c, ε ⟩ ∷ ⟨ λd.d, ε ⟩ ∷ []
--   ⟶ ⟨ λyλz.(xz)(yz), ε ∙ ⟨λaλb.a,ε⟩/x ⟩  ∷ ⟨ λc.c, ε ⟩ ∷ ⟨ λd.d, ε ⟩ ∷ []
--   ⟶ ⟨ λz.(xz)(yz), ε ∙ ⟨λaλb.a,ε⟩/x ∙ ⟨λc.c,ε⟩/y ⟩  ∷ ⟨ λd.d, ε ⟩ ∷ []
--   ⟶ ⟨ (xz)(yz), ε ∙ ⟨λaλb.a,ε⟩/x ∙ ⟨λc.c,ε⟩/y ∙ ⟨λd.d,ε⟩/z ⟩ ∷ []
--   =: ⟨ (xz)(yz), ρ ⟩ ∷ []
--   ⟶ ⟨ xz, ρ ⟩ ∷ ⟨ yz, ρ ⟩ ∷ []
--   ⟶ ⟨ x, ρ ⟩ ∷ ⟨ z, ρ ⟩ ∷⟨ yz, ρ ⟩ ∷ []
--   ⟶ ⟨ λaλb.a, ε ⟩ ∷ ⟨ z, ρ ⟩ ∷⟨ yz, ρ ⟩ ∷ []
--   ⟶ ⟨ λb.a, ε ∙ ⟨z, ρ⟩/a ⟩ ∷ ⟨ yz, ρ ⟩ ∷ []
--   ⟶ ⟨ a, ε ∙ ⟨z, ρ⟩/a ∙ ⟨yz, ρ⟩/b ∷ []
--   ⟶ ⟨ z, ρ ⟩ ∷ []
--   ⟶ ⟨ λd.d, ε ⟩ ∷ []
--
-- At this point, we cannot make any more transitions, and have reached the final state
-- which is a machine representation ⌜I⌝ of the term I.
--
-- We will show in this file that the Krivine machine is in bisimulation with
-- weak head reduction (theorems K→w an w→K).
--
-- A machine state q can be converted back to a closed term ⦅q⦆ by carrying out all the
-- delayed substitutions stored in closures and turning the stack back into
-- a spine of applications.
--
-- We can thus map a each machine transition to 0 or 1 weak head reduction steps (K→w).
-- VAR and APP are purely administrative and map to 0 weak head steps.
-- ABS corresponds to a β-contraction (one weak head step).
-- (The proof of K→w is rather straightforward.)
--
-- Conversely, each weak head step maps to a finite nonempty sequence of machine
-- steps (w→K).  Concretely, we prove that for t ⟶w t' there is a state q
-- such that ⌜t⌝ ⟶* q and ⦅q⦆ = t'.
-- Note that q is not simply ⌜t'⌝ since q by default will have a non-empty stack
-- and contain closures on the stack and in the head.
--
-- Let's prove this direction by induction on t ⟶w t'.
--
-- The β case (λxt)u ⟶w t[u/x] requires us to give machine transitions
-- starting at ⟨ (λxt)u, ε ⟩ ∷ [].  These are
--
--       ⟨ (λxt)u, ε ⟩ ∷ []
--   ⟶ ⟨ λxt, ε ⟩ ∷ ⟨ u, ε ⟩ ∷ []
--   ⟶ ⟨ t, ε ∙ ⟨u, ε⟩/x ⟩ ∷ []
--
-- This state converts back to  ⦅ ⟨t, ε ∙ ⟨u, ε⟩/x⟩ ∷ [] ⦆ = t[u/x].
--
-- The application case t u ⟶w t' u with t ⟶w t' gives us by induction hypothesis
-- a state q such that ⌜t⌝ ⟶* q and ⦅q⦆ = t'.
-- This q is a non-empty list of closures k₀ ∷ ... ∷ kₙ ∷ [].
-- We have that ⌜t u⌝ = ⟨t u, ε⟩ ∷ [] ⟶ ⟨t,ε⟩ ∷ ⟨u,ε⟩ ∷ [] ⟶* k₀ ∷ ... ∷ kₙ ∷ ⟨u,ε⟩ ∷ [].
-- Further ⦅ k₀ ∷ ... ∷ kₙ ∷ ⟨u,ε⟩ ∷ [] ⦆ = ⦅q⦆ u = t' u.  ∎

module Machine.Krivine where

open import Prelude using
  ( ∃; _×_; _,_
  ; _≡_; refl; cong; module ≡; module ≡-Reasoning
  )
open import Prelude.Reduction

open import Term
open import Term.Reduction
open import Term.Substitution renaming (lookup to lookupₛ)
open import Term.Substitution.Properties

private
  variable
    a b c : Ty
    Γ Δ : Context
    x : a ∈ Γ
    t t' u : Term Γ a
    σ σ' : Sub Γ Δ

-- Programs are closed terms

Prg = Term ε

-- Closures are terms paired with an environment.
-- Environments are list of closures.

mutual

  data Clos (a : Ty) : Set where
    ⟨_,_⟩ : (t : Term Γ a) (ρ : Env Γ) → Clos a

  data Env : (Γ : Context) → Set where
    ε : Env ε
    _∙_ : (ρ : Env Γ) (k : Clos a) → Env (Γ ∙ a)

private
  variable
    ρ : Env Γ
    k : Clos a

-- Looking up a variable in an environment

lookup : (ρ : Env Γ) (x : a ∈ Γ) → Clos a
lookup (ρ ∙ k) zero = k
lookup (ρ ∙ k) (suc x) = lookup ρ x

-- A stack is a list of closures (cf. spine)

data Stack : (a c : Ty) → Set where
  []  :  Stack c c
  _∷_ :  (k : Clos a) (s : Stack b c) → Stack (a ⇒ b) c

-- A machine state is a closure in a stack

data State (c : Ty) : Set where
  _∙_ : (k : Clos a) (s : Stack a c) → State c

private
  variable
    s s' : Stack a c
    q q' : State c

-- Machine reduction step

infix 4 _⟶K_

data _⟶K_ : (q q' : State c) → Set where
  var : ⟨ var x   , ρ ⟩ ∙ s        ⟶K  lookup ρ x ∙ s
  abs : ⟨ abs t   , ρ ⟩ ∙ (k ∷ s)  ⟶K  ⟨ t , ρ ∙ k ⟩ ∙ s
  app : ⟨ app t u , ρ ⟩ ∙ s        ⟶K  ⟨ t , ρ ⟩ ∙ (⟨ u , ρ ⟩ ∷ s)

-- Multi-step reduction

infix 4 _⟶K*_

_⟶K*_ : (q q' : State c) → Set
_⟶K*_ {c = c} = Star (_⟶K_ {c = c})

------------------------------------------------------------------------
-- Closure under application

-- Stacks are closed under extension

infixr 5 _++_

_++_ : Stack a b → Stack b c → Stack a c
[]       ++ s' = s'
(k ∷ s)  ++ s' = k ∷ (s ++ s')

snoc : Stack a (b ⇒ c) → Clos b → Stack a c
snoc s k = s ++ (k ∷ [])

-- Machine states are closed under stack extension

infixl 5 _∙ₛ_

_∙ₛ_ : State a → Stack a c → State c
(k ∙ s) ∙ₛ s' = k ∙ (s ++ s')

-- Machine reduction is closed under stack extension

extM : {q q' : State a} {s : Stack a c} → q ⟶K q' → q ∙ₛ s ⟶K q' ∙ₛ s
extM var = var
extM abs = abs
extM app = app

-- Multi-step machine reduction is closed under stack extension

extM* : {q q' : State a} → q ⟶K* q' → {s : Stack a c} → q ∙ₛ s ⟶K* q' ∙ₛ s
extM* [] = []
extM* (r ∷ rs) = extM r ∷ extM* rs

-- Multi-step machine reduction is closed under application

infixl 5 _∙ₜ_

_∙ₜ_ : State (a ⇒ b) → Prg a → State b
q ∙ₜ u = q ∙ₛ (⟨ u , ε ⟩ ∷ [])

appM* : {q q' : State (a ⇒ b)} {u : Prg a} → q ⟶K* q' → q ∙ₜ u ⟶K* q' ∙ₜ u
appM* rs = extM* rs

------------------------------------------------------------------------
-- Unrolling a machine state into a term

-- Transforming a closure into a closed term
-- and an environment into a closed substitution

mutual

  ⦅_⦆ₖ : Clos a → Prg a
  ⦅ ⟨ t , ρ ⟩ ⦆ₖ = sub ⦅ ρ ⦆ₑ t

  ⦅_⦆ₑ : Env Γ → Sub ε Γ
  ⦅ ε ⦆ₑ      =  ε
  ⦅ ρ ∙ k ⦆ₑ  =  ⦅ ρ ⦆ₑ ∙ ⦅ k ⦆ₖ

-- Transforming a stack into a sequence of applications

_∙⦅_⦆ₛ : Prg a → Stack a c → Prg c
t ∙⦅ []    ⦆ₛ  =  t
t ∙⦅ k ∷ s ⦆ₛ  =  app t ⦅ k ⦆ₖ ∙⦅ s ⦆ₛ

-- Transforming a machine state into a closed term

⦅_⦆ : State c → Prg c
⦅ k ∙ s ⦆ = ⦅ k ⦆ₖ ∙⦅ s ⦆ₛ

⦅++⦆ : t ∙⦅ s ++ s' ⦆ₛ ≡ t ∙⦅ s ⦆ₛ ∙⦅ s' ⦆ₛ
⦅++⦆ {s = []}    = refl
⦅++⦆ {s = k ∷ s} = ⦅++⦆ {s = s}

------------------------------------------------------------------------
-- K→w:  Weak head reduction simulates Krivine machine reduction

-- 0 or 1 weak head steps.

infix 4 _⟶w?_

data _⟶w?_ (t u : Term Γ a) : Set where
  whd1 : t ⟶w u → t ⟶w? u
  whd0 : t ≡ u → t ⟶w? u

-- Lemma: ⟶w? is closed under application.

appWhd? : t ⟶w? t' → app t u ⟶w? app t' u
appWhd? (whd1 r)     =  whd1 (appl r)
appWhd? (whd0 refl)  =  whd0 refl

appsWhd? : t ⟶w? t' → t ∙⦅ s ⦆ₛ ⟶w? t' ∙⦅ s ⦆ₛ
appsWhd? {s = []}    r  =  r
appsWhd? {s = k ∷ s} r  =  appsWhd? {s = s} (appWhd? r)

appsWhd : t ⟶w t' → t ∙⦅ s ⦆ₛ ⟶w t' ∙⦅ s ⦆ₛ
appsWhd {s = []}    r  =  r
appsWhd {s = k ∷ s} r  =  appsWhd {s = s} (appl r)

-- Lemma: soundness of environment lookup

lookup-sound : lookupₛ ⦅ ρ ⦆ₑ x ≡ ⦅ lookup ρ x ⦆ₖ
lookup-sound {ρ = ρ ∙ k} {x = zero}  = refl
lookup-sound {ρ = ρ ∙ k} {x = suc x} = lookup-sound {ρ = ρ}

-- Application of a function closure weak-head reduces to the closed body

β-clos : app (sub σ (abs t)) u ⟶w sub (σ ∙ u) t
β-clos {σ = σ} {t = t} {u = u} =
  ≡.subst
    (app (abs (sub (lift σ) t)) u ⟶w_)
    (simp-β-clos {σ = σ}{t = t}{u = u})
    (β {t = sub (lift σ) t} {u = u})

-- Every step in the Krivine machine corresponds to 0 or 1 weak-head reduction steps.
-- Variable lookup and shifting arguments on the stack is 0 weak-head reduction steps,
-- Applying an abstraction is one weak head step.

K→w : q ⟶K q' → ⦅ q ⦆ ⟶w? ⦅ q' ⦆

-- 1 whd step:
K→w (abs {t = t} {ρ = ρ} {k = k} {s = s}) =
  whd1 (appsWhd {s = s} (β-clos {σ = ⦅ ρ ⦆ₑ}{t = t}{u = ⦅ k ⦆ₖ} ))
  -- Goal:  app (abs (sub (lift ⦅ ρ ⦆ₑ) t)) ⦅ k ⦆ₖ ⟶w sub (⦅ ρ ⦆ₑ ∙ ⦅ k ⦆ₖ) t

-- no whd steps:
K→w (var {ρ = ρ} {s = s})  =  whd0 (cong (_∙⦅ s ⦆ₛ) (lookup-sound {ρ = ρ}))
  -- Goal: (lookupₛ ⦅ ρ ⦆ₑ x ∙⦅ s ⦆ₛ) ≡ (⦅ lookup ρ x ⦆ₖ ∙⦅ s ⦆ₛ)
K→w app                    =  whd0 refl

------------------------------------------------------------------------
-- w→K: (Multi-step) Krivine reduction simulates weak head reduction

-- Encoding of a closed term as machine state

⌜_⌝ : Prg c → State c
⌜ t ⌝ = ⟨ t , ε ⟩ ∙ []

-- Some round-trip properties of encoding and decoding

round : ⦅ ⌜ t ⌝ ⦆ ≡ t
round = sub-id

round-ext : ⦅ q ∙ₛ s ⦆ ≡ ⦅ q ⦆ ∙⦅ s ⦆ₛ
round-ext {q = k ∙ s₁} {s = s} = ⦅++⦆ {s = s₁}

round-app : ⦅ q ∙ₜ u ⦆ ≡ app ⦅ q ⦆ u
round-app {q = q} {u = u} = ≡.subst
  (λ v →  ⦅ q ∙ₜ u ⦆ ≡ (app _ v))
  sub-id
  (round-ext {q = q} {s = ⟨ u , ε ⟩ ∷ []})

enc-app : ⌜ app t u ⌝ ⟶K ⌜ t ⌝ ∙ₜ u
enc-app = app

-- The simulation has to be formulated as follows:
-- If t ⟶w t' then ⌜ t ⌝ ⟶K* q for some state q with ⦅ q ⦆ ≡ t'.

w→K : t ⟶w t' → ∃ λ q → ⌜ t ⌝ ⟶K* q × ⦅ q ⦆ ≡ t'

-- Case β: step app and abs
w→K (β {t = t}{u = u}) = _ , app ∷ abs ∷ [] , cong (λ u → sub (sg u) t) sub-id

-- Case appl: step app and continue
w→K (appl {u = u} r) with w→K r
... | q' , rs , refl
    = q' ∙ₜ u , app ∷ appM* rs , round-app {q = q'}
