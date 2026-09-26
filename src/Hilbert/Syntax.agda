module Syntax (Atom : Set) where

-- Formulas: just implicational logic with atoms (propositional variables) drawn from A.

data Form : Set where
  `_  : (X : Atom) → Form
  _⇒_ : (A B : Form) → Form

infix  30 `_
infixr 20 _⇒_

variable
  X Y   : Atom
  A B C : Form

-- Context: lists of assumption

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form) → Cxt

infixl 10 _∙_

variable
  Γ Δ Ξ : Cxt

-- Hypotheses: picking an assumption

data _∈_ (A : Form) : (Γ : Cxt) → Set where
  here : A ∈ Γ ∙ A
  there : (x : A ∈ Γ) → A ∈ Γ ∙ B

infix 8 _∈_

variable
  x y : A ∈ Γ

-- Terms: proofs of a conclusion from assumptions

data _⊢_ (Γ : Cxt) : (A : Form) → Set where
  -- Axioms
  K   : Γ ⊢ A ⇒ B ⇒ A
  S   : Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  -- Hypotheses
  `_  : (x : A ∈ Γ) → Γ ⊢ A
  -- Modus ponens (application)
  _∙_ : (t : Γ ⊢ A ⇒ B) (u : Γ ⊢ A) → Γ ⊢ B

infix 8 _⊢_

variable
  t u : Γ ⊢ A

-- Note:
-- * K represents constant functions; K ∙ t ∙ u shall return t always.
-- * S represents application under an additional hypothesis.
--   S ∙ t ∙ u ∙ v shall distribute v to t and u, giving (t ∙ v) ∙ (u ∙ v).

------------------------------------------------------------------------
-- The deduction theorem.

-- The identity is derivable.

I : Γ ⊢ A ⇒ A
I {A = A} = S ∙ K ∙ K { B = A}

-- Void abstractions are an application of K

abs₀ : (t : Γ ⊢ B) → Γ ⊢ A ⇒ B
abs₀ t = K ∙ t

-- The deduction theorem: abstracting the `here` variable.

abs : (t : Γ ∙ A ⊢ B) → Γ ⊢ A ⇒ B
-- Axioms do not use any assumption, so also not variable `here`, thus,
-- the abstraction is void.
abs K = abs₀ K
abs S = abs₀ S
-- A proof by assumption other then `here` does not use variable `here` either.
abs (` (there x)) = abs₀ (` x)
-- Abstracting the assumption `here` is the identity `A ⇒ A`.
abs (` here) = I
-- Abstracting in an application requires us to abstract in both parts
-- and combine the parts with S.
abs (t ∙ u) = S ∙ abs t ∙ abs u

------------------------------------------------------------------------
-- Substitution
--
-- Γ ⊢ₛ Δ states that all propositions in Δ are provable from hypotheses Γ.

data _⊢ₛ_ (Γ : Cxt) : (Δ : Cxt) → Set where
  idₛ : Γ ⊢ₛ Γ
  _∙_ : (σ : Γ ⊢ₛ Δ) (t : Γ ⊢ A) → Γ ⊢ₛ Δ ∙ A

infix 8 _⊢ₛ_
variable
  σ : Γ ⊢ₛ Δ

-- Substitution for a hypothesis.
-- If A ∈ Δ and we can prove all of Δ from Γ,
-- surely we can prove A from Γ by just picking the respective
-- proof from Γ ⊢ₛ Δ.

lookup : (σ : Γ ⊢ₛ Δ) (x : A ∈ Δ) → Γ ⊢ A
lookup idₛ     x         = ` x
lookup (σ ∙ t) here      = t
lookup (σ ∙ t) (there x) = lookup σ x

-- Substitution: if we can prove A from Δ and all of Δ from Γ,
-- surely we can prove A from Γ.

sub : (σ : Γ ⊢ₛ Δ) (t : Δ ⊢ A) → Γ ⊢ A
sub σ K       = K
sub σ S       = S
sub σ (` x)   = lookup σ x
sub σ (t ∙ u) = sub σ t ∙ sub σ u

-- Substitutions form a category: there is an identity substitution
-- (by definition) and substitutions can be composed.

-- Composition is compₛ σ₁ σ₂ amounts to applying the substitution σ₁
-- to each entry in the substitution σ₂.

compₛ : (σ₁ : Γ ⊢ₛ Δ) (σ₂ : Δ ⊢ₛ Ξ) → Γ ⊢ₛ Ξ
compₛ σ₁ idₛ      = σ₁
compₛ σ₁ (σ₂ ∙ t) = compₛ σ₁ σ₂ ∙ sub σ₁ t

-- The "meta deduction theorem" Γ ∙ A ⊢ B → (Γ ⊢ A → Γ ⊢ B)
-- is just an instance of substitution.

sub1 : (t : Γ ∙ A ⊢ B) (u : Γ ⊢ A) → Γ ⊢ B
sub1 t u = sub (idₛ ∙ u) t

------------------------------------------------------------------------
-- Weakening
--
-- If we can prove A from Δ, we should still be able to prove A if we
-- add assumptions to Δ, arriving at an extended context Γ.
--
-- We define Γ ≤ Δ to mean that Δ is a subsequence of Γ.
-- The direction of _≤_ might be counterintuitive (since Γ is bigger),
-- but it reflects the role of contexts as lists of hypotheses
-- used to prove a theorem A.
-- Going from Γ ⊢ A to Δ ⊢ A, dropping some hypotheses from Γ,
-- makes the proof of A "stronger"; it still works when less hypotheses
-- actually hold.
-- Conversely, going from Δ ⊢ A to Γ ⊢ A is weakening the proof
-- by adding in spurious hypothesis.
-- In this sense, we may call Γ weaker than Δ, justifying Γ ≤ Δ.

-- The constructors of Γ ≤ Δ should be understood as instructions
-- how to act while walking through Γ in order to arrive at Δ:
-- Each hypothesis from Γ can be either kept or dropped ("skipped").

data _≤_ : (Γ Δ : Cxt) → Set where
  ε    : ε ≤ ε
  skip : (ρ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  keep : (ρ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

infix 8 _≤_

-- Each context is a weakening of the empty one: just skip everything.

emptyʷ : Γ ≤ ε
emptyʷ {Γ = ε}     = ε
emptyʷ {Γ = Γ ∙ A} = skip emptyʷ

-- Weakening is a preorder: reflexive and transitive.

idʷ : Γ ≤ Γ
idʷ {Γ = ε} = ε
idʷ {Γ = Γ ∙ A} = keep idʷ

-- Showing transitivity of weakening:
-- Compose two subsequent list of instructions how to arrive at a subsequence
-- to a single such list.
compʷ : (ρ₁ : Γ ≤ Δ) (ρ₂ : Δ ≤ Ξ) → Γ ≤ Ξ
compʷ ε         ρ₂        = ρ₂
compʷ (skip ρ₁) ρ₂        = skip (compʷ ρ₁ ρ₂)
compʷ (keep ρ₁) (skip ρ₂) = skip (compʷ ρ₁ ρ₂)
compʷ (keep ρ₁) (keep ρ₂) = keep (compʷ ρ₁ ρ₂)

-- Weakening is also anti-symmetric, thus, forming a partial order.
-- However, the proof is more complicated, and we do not need this fact.
