-- Call-by-name abstract machine

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

-- Programs are closed term

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
-- Weak head reduction simulates Krivine machine reduction

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

-- app (sub σ (abs t)) u ≡ sub (σ ∙ u) t

lem0 : (sub (lift σ) t) [ u ]₀ ≡ sub (σ ∙ u) t
lem0 {σ = σ} {t = t} {u = u} = begin
   sub (sg u) (sub (lift σ) t)        ≡⟨ sub-comp {σ = sg u} {σ' = lift σ} {t = t} ⟩
   sub (compSS (sg u) (weak σ) ∙ u) t ≡⟨ cong (λ σ → sub (σ ∙ u) t) comp-sg-weak  ⟩
   sub (σ ∙ u) t   ∎
  where open ≡-Reasoning

-- Application of a function closure weak-head reduces to the closed body

lem : app (sub σ (abs t)) u ⟶w sub (σ ∙ u) t
lem {σ = σ} {t = t} {u = u} =
  ≡.subst
    (app (abs (sub (lift σ) t)) u ⟶w_)
    (lem0 {σ = σ}{t = t}{u = u})
    (β {t = sub (lift σ) t} {u = u})

-- Every step in the Krivine machine corresponds to 0 or 1 weak-head reduction steps.
-- Variable lookup and shifting arguments on the stack is 0 weak-head reduction steps,
-- Applying an abstraction is one weak head step.

K→w : q ⟶K q' → ⦅ q ⦆ ⟶w? ⦅ q' ⦆

-- 1 whd step:
K→w (abs {t = t} {ρ = ρ} {k = k} {s = s}) = whd1 (appsWhd {s = s} (lem {σ = ⦅ ρ ⦆ₑ}{t = t}{u = ⦅ k ⦆ₖ} ))
  -- Goal:  app (abs (sub (lift ⦅ ρ ⦆ₑ) t)) ⦅ k ⦆ₖ ⟶w sub (⦅ ρ ⦆ₑ ∙ ⦅ k ⦆ₖ) t

-- no whd steps:
K→w (var {ρ = ρ} {s = s})  =  whd0 (cong (_∙⦅ s ⦆ₛ) (lookup-sound {ρ = ρ}))
  -- Goal: (lookupₛ ⦅ ρ ⦆ₑ x ∙⦅ s ⦆ₛ) ≡ (⦅ lookup ρ x ⦆ₖ ∙⦅ s ⦆ₛ)
K→w app                    =  whd0 refl


------------------------------------------------------------------------
-- (Multi-step) Krivine reduction simulates weak head reduction

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


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
