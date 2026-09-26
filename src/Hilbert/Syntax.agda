module Syntax (Atom : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_)

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
-- Kripke models

-- A kripke model is characterized by a preorder of worlds and
-- a relation (forcing) monotone in worlds
-- that determines which atoms hold at which world.
record Kripke : Set₁ where
  field
    -- A set of worlds.
    World : Set
    -- A preorder on worlds.
    -- w ≤ w' shall mean w is a future of w'.
    _≤_ : (w w' : World) → Set
    refl : ∀{w} → w ≤ w
    trans : ∀{w₁ w₂ w₃} → w₁ ≤ w₂ → w₂ ≤ w₃ → w₁ ≤ w₃
    -- A forcing relation on atoms.
    _⊩ₐ_ : World → Atom → Set
    -- Forcing is monotone: true atoms stay true in any future.
    monₐ : ∀{w w' A} → w ≤ w' → w' ⊩ₐ A → w ⊩ₐ A

module Model (Structure : Kripke) (open Kripke Structure) where

  -- The forcing relation extends forcing for atoms to all formulas.
  -- Implication A ⇒ B shall only hold in world w
  -- if the meta-implication (_⊩ A → _⊩ B) holds not just in w but also
  -- in all of its futures w' ≤ w.
  -- This promotes implications from mere coincidences
  -- to laws of consequence.

  private variable
    w w' : World

  infix 8 _⊩_

  _⊩_ : (w : World) (A : Form) → Set
  w ⊩ (` X)   = w ⊩ₐ X
  w ⊩ (A ⇒ B) = ∀{w'} → w' ≤ w → w' ⊩ A → w' ⊩ B

  -- The forcing relation stays monotone.
  -- This is proven by induction on the formula.

  mon : ∀{w w' A} (ρ : w ≤ w') (a : w' ⊩ A) → w ⊩ A
  mon {A = ` X  } ρ a = monₐ ρ a
  mon {A = A ⇒ B} ρ f = λ ρ' a → f (trans ρ' ρ) a

  -- K and S are forced always

  ⊩K : w ⊩ A ⇒ B ⇒ A
  ⊩K {A = A} _ a η b = mon {A = A} η a

  ⊩S : w ⊩ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  ⊩S _ f η g η' a = f (trans η' η) a refl (g η' a)

  -- Kripke application

  _⊩∙_ : w ⊩ A ⇒ B → w ⊩ A → w ⊩ B
  f ⊩∙ a = f refl a
  infixl 10 _⊩∙_; {-# INLINE _⊩∙_ #-}

-- We can give a countermodel to the Peirce formula.

Peirce : (X Y : Atom) → Form
Peirce X Y = ((` X ⇒ ` Y) ⇒ ` X) ⇒ ` X

module PeirceStructure (X Y : Atom) where

  -- We need two worlds: future ≤ now.

  data World : Set where
    now future : World

  variable
    w w' w₁ w₂ w₃ : World

  data _≤_ : (w w' : World) → Set where
    now    : w      ≤ now
    future : future ≤ w

  refl : w ≤ w
  refl {w = now}    = now
  refl {w = future} = future

  trans : (ρ : w₁ ≤ w₂) (ρ' : w₂ ≤ w₃) → w₁ ≤ w₃
  trans future _ = future
  trans now  now = now

  -- To construct the countermodel for Peirce, let us consider some cases.
  -- If X holds now, the formula is valid now and in the future.
  -- So let X not hold now.
  -- If X does not hold in the future either, then X ⇒ Y is always true,
  -- so (X ⇒ Y) ⇒ X is always false, so the formula is always valid.
  -- So X must be true in the future if we want to refute Peirce.
  -- Say Y is true always, then Perice simplifies to X ⇒ X and is not refutable.
  -- If Y is false always, then the formula simplifies to X ⇒ X now

  data _⊩ₐ_ : World → Atom → Set where
    futureX : future ⊩ₐ X

  monₐ : ∀{w w' Z} (ρ : w ≤ w') (a : w' ⊩ₐ Z) → w ⊩ₐ Z
  monₐ future futureX = futureX

module RefutePeirce (X Y : Atom) (X≠Y : X ≢ Y) where
  open module S = PeirceStructure X Y
  open Model record{ S }

  -- Y is never forced.
  neverY : w ⊩ₐ Y → ⊥
  neverY futureX = X≠Y ≡.refl

  -- X is not forced now.
  now¬X : now ⊩ₐ X → ⊥
  now¬X ()

  -- Peirce is not forced now.
  refute : now ⊩ Peirce X Y → ⊥
  refute f = now¬X do
    f now λ where
      future         g → futureX
      (now {future}) g → futureX
      (now {now})    g → ⊥-elim (neverY (g future futureX))

------------------------------------------------------------------------
-- Soundness: each derivable formula is valid in each Kripke model

module Soundness (Structure : Kripke) where

  open Kripke Structure
  open Model Structure

  private variable w w' : World

  -- We extend forcing to contexts: each formula in the context is forced.
  data _⊩ₛ_ (w : World) : (Γ : Cxt) → Set where
    ε   : w ⊩ₛ ε
    _∙_ : (δ : w ⊩ₛ Γ) (a : w ⊩ A) → w ⊩ₛ Γ ∙ A
  infix 8 _⊩ₛ_ _⊧_

  monₛ : (ρ : w ≤ w') (δ : w' ⊩ₛ Γ) → w ⊩ₛ Γ
  monₛ ρ ε = ε
  monₛ ρ (_∙_ {A = A} δ a) = monₛ ρ δ ∙ mon {A = A} ρ a

  -- A sequent Γ ⊢ A is valid in the given Structure
  -- if all worlds that force Γ also force A.

  _⊧_ : (Γ : Cxt) (A : Form) → Set
  Γ ⊧ A = ∀{w} → w ⊩ₛ Γ → w ⊩ A

  -- Lemma: assumptions are valid (just a lookup).

  ⦅_⦆ₓ : A ∈ Γ → Γ ⊧ A
  ⦅ here ⦆ₓ    (ρ ∙ a) = a
  ⦅ there x ⦆ₓ (ρ ∙ a) = ⦅ x ⦆ₓ ρ

  -- Lemma: K is valid
  validK : Γ ⊧ A ⇒ B ⇒ A
  validK {A = A} _ _ a η _ = mon {A = A} η a

  -- Lemma: S is valid
  validS : Γ ⊧ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  validS _ _ f η g η' a = f (trans η' η) a refl (g η' a)

  -- Lemma: application is valid
  apply : Γ ⊧ A ⇒ B → Γ ⊧ A → Γ ⊧ B
  apply f g ρ = f ρ refl (g ρ)

  -- Soundness: all derivable sequents Γ ⊢ A are valid.

  ⦅_⦆ : Γ ⊢ A → Γ ⊧ A
  ⦅ K {A = A} {B = B} ⦆         ρ = ⊩K {A = A} {B = B}
  ⦅ S {A = A} {B = B} {C = C} ⦆ ρ = ⊩S {A = A} {B = B} {C = C}
  ⦅ ` x ⦆                       ρ = ⦅ x ⦆ₓ ρ
  ⦅ t ∙ u ⦆                     ρ = ⦅ t ⦆ ρ refl (⦅ u ⦆ ρ)

module PeirceNotDerivable (X Y : Atom) (X≠Y : X ≢ Y) where
  open RefutePeirce X Y X≠Y
  open Soundness record{ S }

  peirceFalse : ε ⊢ Peirce X Y → ⊥
  peirceFalse t = refute (⦅ t ⦆ ε)

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

module Weakening where

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

  -- A weakening maps variables to their new index.

  weakₓ : (ρ : Γ ≤ Δ) (x : A ∈ Δ) → A ∈ Γ
  weakₓ (keep ρ) here      = here
  weakₓ (keep ρ) (there x) = there (weakₓ ρ x)
  weakₓ (skip ρ) x         = there (weakₓ ρ x)

  -- Derivation is preserved under weakening.

  weak : (ρ : Γ ≤ Δ) (t : Δ ⊢ A) → Γ ⊢ A
  weak ρ K       = K
  weak ρ S       = S
  weak ρ (` x)   = ` weakₓ ρ x
  weak ρ (t ∙ u) = weak ρ t ∙ weak ρ u

------------------------------------------------------------------------
-- Normal forms

module NormalForms where
  mutual
    infix 8 _⊢ᵤ_ _⊢ₙ_

    -- Variable headed normal forms: never reduce even under further applications.
    -- These are also called neutral.

    data _⊢ᵤ_ (Γ : Cxt) : (A : Form) → Set where
      `_  : (x : A ∈ Γ) → Γ ⊢ᵤ A
      _∙_ : (u : Γ ⊢ᵤ A ⇒ B) (n : Γ ⊢ₙ A) → Γ ⊢ᵤ B

    -- Normal forms (unless applied to further arguments).

    data _⊢ₙ_ (Γ : Cxt) : (A : Form) → Set where
      -- Neutrals are normal
      ne  : (u : Γ ⊢ᵤ A) → Γ ⊢ₙ A
      -- Underapplied combinators are normal
      K   : Γ ⊢ₙ A ⇒ B ⇒ A
      K∙  : Γ ⊢ₙ A → Γ ⊢ₙ B ⇒ A
      S   : Γ ⊢ₙ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
      S∙  : Γ ⊢ₙ A ⇒ B ⇒ C → Γ ⊢ₙ (A ⇒ B) ⇒ A ⇒ C
      S∙∙ : Γ ⊢ₙ A ⇒ B ⇒ C → Γ ⊢ₙ (A ⇒ B) → Γ ⊢ₙ A ⇒ C

  -- Normal forms are closed under weakening.
  open Weakening

  mutual

    weakᵤ : (ρ : Γ ≤ Δ) (u : Δ ⊢ᵤ A) → Γ ⊢ᵤ A
    weakᵤ ρ (` x)      = ` weakₓ ρ x
    weakᵤ ρ (u ∙ n)    = weakᵤ ρ u ∙ weakₙ ρ n

    weakₙ : (ρ : Γ ≤ Δ) (n : Δ ⊢ₙ A) → Γ ⊢ₙ A
    weakₙ ρ (ne u)     = ne (weakᵤ ρ u)
    weakₙ ρ K          = K
    weakₙ ρ (K∙ n)     = K∙ (weakₙ ρ n)
    weakₙ ρ S          = S
    weakₙ ρ (S∙ n)     = S∙ (weakₙ ρ n)
    weakₙ ρ (S∙∙ n n₁) = S∙∙ (weakₙ ρ n) (weakₙ ρ n₁)

  -- The abstraction theorem for normal forms.

  Iₙ : Γ ⊢ₙ A ⇒ A
  Iₙ {A = A} = S∙∙ K (K {B = A})

  mutual
    absᵤ : Γ ∙ A ⊢ᵤ B → Γ ⊢ₙ A ⇒ B
    absᵤ (` here)    = Iₙ
    absᵤ (` there x) = K∙ (ne (` x))
    absᵤ (u ∙ n)     = S∙∙ (absᵤ u) (absₙ n)

    absₙ : Γ ∙ A ⊢ₙ B → Γ ⊢ₙ A ⇒ B
    absₙ (ne u)     = absᵤ u
    absₙ K          = K∙ K
    absₙ (K∙ n)     = S∙∙ (K∙ K) (absₙ n)
    absₙ S          = K∙ S
    absₙ (S∙ n)     = S∙∙ (K∙ S) (absₙ n)
    absₙ (S∙∙ n n₁) = S∙∙ (S∙∙ (K∙ S) (absₙ n)) (absₙ n₁)


------------------------------------------------------------------------
-- Normalization by evaluation.

-- We instantiate our generic soundness theorem to the Kripke model
-- where worlds are contexts under the preorder of weakening
-- and forcing atoms A in a world Γ is witnessed by a neutral derivation Γ ⊢ᵤ A.

module NbEStructure where
  World = Cxt
  open Weakening public using (_≤_) renaming (idʷ to refl; compʷ to trans)
  open NormalForms public using (_⊢ᵤ_) renaming (weakᵤ to monₐ)

  _⊩ₐ_ : World → Atom → Set
  Γ ⊩ₐ X = Γ ⊢ᵤ ` X

module NbE where

  s : Kripke
  s = record{ NbEStructure }

  open Model s
  open Soundness s
  open NormalForms
  open Weakening

  -- The soundness theorem can be utilized to give us Γ ⊩ A from Γ ⊢ A.
  -- We just need to get a normal form Γ ⊢ₙ A out of Γ ⊩ A.
  -- This process is called reification.
  --
  -- For atomic A, this is trivial, because then Γ ⊩ A is Γ ⊢ᵤ A.
  -- It is more tricky for non-atomic A.
  --
  -- Γ ⊩ A ⇒ B is made of functions f : Δ ≤ Γ → Δ ⊩ A → Δ ⊩ B;
  -- we have to turn them back into normal forms.
  -- We choose Δ = Γ ∙ A and apply f to the weakening skip idʷ : Γ ∙ A ≤ Γ
  -- and some argument Γ ∙ A ⊩ A.
  -- This gives us Γ ∙ A ⊩ B which we recursively turn into a normal form Γ ∙ A ⊢ₙ B
  -- and with the abstraction theorem for normal forms we get Γ ⊢ₙ A ⇒ B.
  --
  -- The question is where we get Γ ∙ A ⊩ A from.
  -- We know that there is a trivial, even neutral derivation Γ ∙ A ⊢ᵤ A;
  -- it is just the last variable ("here").
  -- We want to "reflect" it into the model.
  --
  -- If A is atomic, we thus already have Γ ∙ A ⊩ A.
  -- Again, it is more tricky for implications.
  --
  -- We more generally define reflection of neutral derivations Γ ⊢ᵤ A into the model Γ ⊩ A.
  -- In case of implication, we have Γ ⊢ᵤ A ⇒ B and need to produce Δ ⊩ B for any Δ ≤ Γ and Δ ⊩ A.
  -- We weaken the neutral derivation to Δ ⊢ᵤ A ⇒ B and apply it to the reification Δ ⊢ₙ A of Δ ⊩ A.
  -- Thus we have a neutral Δ ⊢ᵤ B that we can recursively reflect to get Δ ⊩ B.
  --
  -- Reflection and reification are defined mutually by induction on the formula.
  mutual
    reify : Γ ⊩ A → Γ ⊢ₙ A
    reify {A = ` X}   u = ne u
    reify {A = A ⇒ B} f = absₙ (reify (f (skip idʷ) (reflect {A = A} (` here))))

    reflect : Γ ⊢ᵤ A → Γ ⊩ A
    reflect {A = ` X}   u     = u
    reflect {A = A ⇒ B} u ρ a = reflect (weakᵤ ρ u ∙ reify a)

  -- An identity environment in the model is needed to instantiate the soundness theorem.
  -- It is constructed by reflecting each assumption in Γ, using weakening to make the induction on Γ work.
  ⊩ₛid : Γ ⊩ₛ Γ
  ⊩ₛid {Γ = ε} = ε
  ⊩ₛid {Γ = Γ ∙ A} = monₛ (skip idʷ) (⊩ₛid {Γ = Γ}) ∙ reflect {A = A} (` here)

  -- For each derivation there is also a normal one.
  -- This is now just evaluation (soundness) in the reflected identity environment
  -- followed by reification.
  norm : Γ ⊢ A → Γ ⊢ₙ A
  norm t  = reify (⦅ t ⦆ ⊩ₛid)
