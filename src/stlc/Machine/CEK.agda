-- Call-by-value abstract machine CEK
-- Control-Environment-"Kontinuation" (Felleisen, Friedman, 1986)

module Machine.CEK where

open import Prelude using
  ( ∃; _×_; _,_
  ; _≡_; refl; cong; module ≡; module ≡-Reasoning
  )
open import Prelude.Reduction

open import Term
open import Term.CallByValue
open import Term.Substitution as Sub renaming (lookup to lookupₛ)
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

-- Values are lambda abstractions in an environment
-- Environments are lists of values

mutual

  data Val : Ty → Set where
    ⟨λ_,_⟩ : (t : Term (Γ ∙ a) b) (ρ : Env Γ) → Val (a ⇒ b)

  data Env : (Γ : Context) → Set where
    ε : Env ε
    _∙_ : (ρ : Env Γ) (v : Val a) → Env (Γ ∙ a)

private
   variable
     ρ ρ' : Env Γ
     v : Val a

-- Looking up a variable in an environment

lookup : (ρ : Env Γ) (x : a ∈ Γ) → Val a
lookup (ρ ∙ k) zero = k
lookup (ρ ∙ k) (suc x) = lookup ρ x

-- Stacks are continuations.
-- We might continue after having evaluated a function or an argument.

infix 6 _∙□

data Frame : (a c : Ty) → Set where
  -- a function value to be applied to the evaluated argument
  _∙□ : (f : Val (a ⇒ b)) → Frame a b
  -- an unevaluated argument as closure
  □∙⟨_,_⟩ : (t : Term Γ a) (ρ : Env Γ) → Frame (a ⇒ b) b

data Stack : (a c : Ty) → Set where
  []  : Stack c c
  _∷_ : (k : Frame a b) (s : Stack b c) → Stack a c

-- A machine state is term ("Control") in some environment under some stack ("continuation),
-- or some value under a continuation.

infixl 5 _[_]∙_ -- _∙_  -- Parse error

data State (c : Ty) : Set where
  _[_]∙_ : (t : Term Γ a) (ρ : Env Γ) (s : Stack a c) → State c
  _∙_    : (v : Val a) (s : Stack a c) → State c

private
  variable
    k k' : Frame a c
    s s' : Stack a c
    q q' : State c

-- Machine reduction step

infix 4 _⟶C_

data _⟶C_ : (q q' : State c) → Set where

  -- Term states
  var   : var x      [ ρ ]∙ s  ⟶C  lookup ρ x ∙ s
  abs   : (abs t)    [ ρ ]∙ s  ⟶C  ⟨λ t , ρ ⟩ ∙ s
  app   : (app t u)  [ ρ ]∙ s  ⟶C  t [ ρ ]∙ (□∙⟨ u , ρ ⟩ ∷ s)

  -- Value states
  -- Evaluate the argument sitting on top of the stack:
  eval  : v ∙ (□∙⟨ u , ρ ⟩   ∷ s)  ⟶C  u [ ρ ]∙ (v ∙□ ∷ s)
  -- Call the function sitting on top of the stack (β):
  call  : v ∙ (⟨λ t , ρ ⟩ ∙□ ∷ s)  ⟶C  t [ ρ ∙ v ]∙ s

-- Multiple machine steps

infix 4 _⟶C*_

_⟶C*_ : (q q' : State c) → Set
_⟶C*_ = Star _⟶C_

------------------------------------------------------------------------
-- Machine reductions are closed under stack extensions


-- Stacks are closed under extension

infixr 5 _++_

_++_ : Stack a b → Stack b c → Stack a c
[]       ++ s' = s'
(k ∷ s)  ++ s' = k ∷ (s ++ s')


-- Machine states are closed under stack extension

infixl 5 _∙ₛ_

_∙ₛ_ : State a → Stack a c → State c
(t [ ρ ]∙ s) ∙ₛ s' = t [ ρ ]∙ (s ++ s')
(v      ∙ s) ∙ₛ s' = v ∙ (s ++ s')

-- Machine reduction is closed under stack extension

extM : {q q' : State a} {s : Stack a c} → q ⟶C q' → q ∙ₛ s ⟶C q' ∙ₛ s
extM var = var
extM abs = abs
extM app = app
extM eval = eval
extM call = call

-- Multi-step machine reduction is closed under stack extension

extM* : {q q' : State a} → q ⟶C* q' → {s : Stack a c} → q ∙ₛ s ⟶C* q' ∙ₛ s
extM* [] = []
extM* (r ∷ rs) = extM r ∷ extM* rs

-- Multi-step machine reduction is closed under application

infixl 5 _∙ₖ_

_∙ₖ_ : State a → Frame a b → State b
q ∙ₖ k = q ∙ₛ (k ∷ [])

appM* : q      ⟶C* q'
      → q ∙ₖ k ⟶C* q' ∙ₖ k
appM* rs = extM* rs


------------------------------------------------------------------------
-- Translation between machine states and terms

-- Decoding of values and environments

mutual

  ⦅_⦆ᵥ : Val c → Prg c
  ⦅ ⟨λ t , ρ ⟩ ⦆ᵥ = sub ⦅ ρ ⦆ₑ (abs t)

  ⦅_⦆ₑ : Env Γ → Sub ε Γ
  ⦅ ε ⦆ₑ     = ε
  ⦅ ρ ∙ v ⦆ₑ = ⦅ ρ ⦆ₑ ∙ ⦅ v ⦆ᵥ

-- Decoding of stacks as continuations

_∙⦅_⦆ₖ : Prg a → Frame a c → Prg c
t ∙⦅ f ∙□ ⦆ₖ         = app ⦅ f ⦆ᵥ t
t ∙⦅ □∙⟨ u , ρ ⟩ ⦆ₖ  = app t (sub ⦅ ρ ⦆ₑ u)

_∙⦅_⦆ₛ : Prg a → Stack a c → Prg c
t ∙⦅ []    ⦆ₛ  =  t
t ∙⦅ k ∷ s ⦆ₛ  =  t ∙⦅ k ⦆ₖ ∙⦅ s ⦆ₛ

-- Decoding of states as closed terms

⦅_⦆ : State c → Prg c
⦅ t [ ρ ]∙ s ⦆ = sub ⦅ ρ ⦆ₑ t ∙⦅ s ⦆ₛ
⦅ v ∙ s ⦆ = ⦅ v ⦆ᵥ ∙⦅ s ⦆ₛ

⦅++⦆ : t ∙⦅ s ++ s' ⦆ₛ ≡ t ∙⦅ s ⦆ₛ ∙⦅ s' ⦆ₛ
⦅++⦆ {s = []}    = refl
⦅++⦆ {s = k ∷ s} = ⦅++⦆ {s = s}

-- The decoding of a CEK-value is a CBV value

valVal : Value ⦅ v ⦆ᵥ
valVal {v = ⟨λ t , ρ ⟩} = abs

-- Encoding a term as machine state

⌜_⌝ : Prg c → State c
⌜ t ⌝ = t [ ε ]∙ []

------------------------------------------------------------------------
-- Simulation: every CEK step is at most one weak cbv step

-- 0 or 1 weak cbv steps.

infix 4 _⟶v?_

data _⟶v?_ (t u : Term Γ a) : Set where
  wv1 : t ⟶v u → t ⟶v? u
  wv0 : t ≡ u → t ⟶v? u

-- Lemma: ⟶v? is closed under evaluation stacks.

appVₖ : t ⟶v t' → t ∙⦅ k ⦆ₖ ⟶v t' ∙⦅ k ⦆ₖ
appVₖ {k = ⟨λ t , ρ ⟩ ∙□}  r  =  appr r
appVₖ {k = □∙⟨ t , ρ ⟩}    r  =  appl r

appsV : t ⟶v t' → t ∙⦅ s ⦆ₛ ⟶v t' ∙⦅ s ⦆ₛ
appsV {s = []}    r  =  r
appsV {s = k ∷ s} r  =  appsV {s = s} ((appVₖ r))

appV?ₖ : t ⟶v? t' → t ∙⦅ k ⦆ₖ ⟶v? t' ∙⦅ k ⦆ₖ
appV?ₖ (wv1 r)     =  wv1 (appVₖ r)
appV?ₖ (wv0 refl)  =  wv0 refl

appsV? : t ⟶v? t' → t ∙⦅ s ⦆ₛ ⟶v? t' ∙⦅ s ⦆ₛ
appsV? {s = []}    r  =  r
appsV? {s = k ∷ s} r  =  appsV? {s = s} ((appV?ₖ r))

-- Lemma: soundness of environment lookup

lookup-sound : Sub.lookup ⦅ ρ ⦆ₑ x ≡ ⦅ lookup ρ x ⦆ᵥ
lookup-sound {ρ = ρ ∙ k} {x = zero}  = refl
lookup-sound {ρ = ρ ∙ k} {x = suc x} = lookup-sound {ρ = ρ}

-- Application of a function closure weak cbv reduces to the closed body

β-clos : Value u → app (sub σ (abs t)) u ⟶v sub (σ ∙ u) t
β-clos  {u = u} {σ = σ} {t = t} v =
  ≡.subst
    (app (abs (sub (lift σ) t)) u ⟶v_)
    (simp-β-clos {σ = σ}{t = t}{u = u})
    (βᵥ {t = sub (lift σ) t} v)

CEK→v : q ⟶C q' → ⦅ q ⦆ ⟶v? ⦅ q' ⦆
-- The term steps are no-ops in ⟶v
CEK→v (var {ρ = ρ} {s = s}) = wv0 (cong (_∙⦅ s ⦆ₛ) (lookup-sound {ρ = ρ}))
CEK→v abs = wv0 refl
CEK→v app = wv0 refl
CEK→v eval = wv0 refl
-- Only the call step is a β contraction
CEK→v (call {v = v} {t = t} {ρ = ρ} {s = s}) =
  wv1 (appsV {s = s} (β-clos {u = ⦅ v ⦆ᵥ} {σ = ⦅ ρ ⦆ₑ} {t = t} (valVal {v = v})))


------------------------------------------------------------------------
-- (Multi-step) CEK reduction simulates weak cvb reduction

round-ext : ⦅ q ∙ₛ s ⦆ ≡ ⦅ q ⦆ ∙⦅ s ⦆ₛ
round-ext {q = _      ∙ s₁} {s = s} = ⦅++⦆ {s = s₁}
round-ext {q = _ [ _ ]∙ s₁} {s = s} = ⦅++⦆ {s = s₁}

round-app : ⦅ q ∙ₖ □∙⟨ u , ε ⟩ ⦆ ≡ app ⦅ q ⦆ u
round-app {q = q} {u = u} = ≡.trans
  (round-ext {q = q} {s = □∙⟨ u , ε ⟩ ∷ []})
  (cong (app ⦅ q ⦆) sub-id)

round-beta : ⦅ q ∙ₛ ((⟨λ t , ε ⟩ ∙□) ∷ []) ⦆ ≡ app (abs t) ⦅ q ⦆
round-beta {q = q} {t = t} = ≡.trans
  (round-ext {q = q} {s = (⟨λ t , ε ⟩ ∙□) ∷ []})
  (cong (λ t → app (abs t) ⦅ q ⦆) sub-id)

-- The simulation has to be formulated as follows:
-- If t ⟶v t' then ⌜ t ⌝ ⟶C* q for some state q with ⦅ q ⦆ ≡ t'.

v→CEK : t ⟶v t' → ∃ λ q → ⌜ t ⌝ ⟶C* q × ⦅ q ⦆ ≡ t'

-- For beta, we first move to the function, observe it is a value, move this to the stack,
-- observe that the argument is also a value, so we can execute the call.
v→CEK (βᵥ {u = abs u} {t = t} abs) =  _ , app ∷ abs ∷ eval ∷ abs ∷ call ∷ [] , cong (λ u → sub (sg (abs u)) t) sub-id

v→CEK (appl {t = t} {t' = t'} {u = u} r) with v→CEK r
... | q' , rs , refl = q' ∙ₖ □∙⟨ u , ε ⟩ , app ∷ appM* rs , round-app {q = q'}

v→CEK (appr {u = u} {u' = u'} {t = t} r) with v→CEK r
... | q' , rs , refl = q' ∙ₖ ⟨λ t , ε ⟩ ∙□ , app ∷ abs ∷ eval ∷ appM* rs , round-beta {q = q'}


-- TRASH

  -- abs   : (abs t)    [ ρ ]∙ (□∙⟨ u , ρ' ⟩ ∷ s) ⟶C  u [ ρ' ] (⟨λ t , ρ ⟩ ∙□ ∷ s)
  -- var[] : x [ ρ ] [] ⟶C done (lookup ρ x)
  -- varA  : x [ ρ ] (□∙ u ∷ s) ⟶C u [ ρ ] (lookup ρ x ∙□ ∷ s)
  -- varF  : x [ ρ ] (⟨λ t , ρ' ⟩ ∙□ ∷ s) ⟶C t [ ρ' ∙ lookup ρ x ] s
  -- abs   : abs t [ ρ ] (□∙ u ∷


-- -- -- Constructing a state from function value and stack

-- valState : (v : Val a) (s : Stack a c) → State c
-- valState ⟨λ t , ρ ⟩ (□∙ u ∷ s)

-- -- Lookup (x : a ∈ Γ) (ρ : Env Γ) (s : Stack a c) → State


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
