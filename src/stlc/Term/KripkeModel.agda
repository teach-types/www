module Term.KripkeModel where

open import Prelude hiding (refl; trans)
open import Term using (`_; _⇒_; _∈_; zero; suc; ε; _∙_)
open import Term using (abs) renaming
  (BaseTy to Atom; Ty to Form; Context to Cxt
  ; Term to infix 4 _⊢_; var to `_; app to infixl 5 _∙_)

private
  variable
    A B C : Form
    Γ Δ Ξ : Cxt

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
  infixl 5 _∙_
  infix 4 _⊩ₛ_ _⊧_

  monₛ : (ρ : w ≤ w') (δ : w' ⊩ₛ Γ) → w ⊩ₛ Γ
  monₛ ρ ε = ε
  monₛ ρ (_∙_ {A = A} δ a) = monₛ ρ δ ∙ mon {A = A} ρ a

  -- A sequent Γ ⊢ A is valid in the given Structure
  -- if all worlds that force Γ also force A.

  _⊧_ : (Γ : Cxt) (A : Form) → Set
  Γ ⊧ A = ∀{w} → w ⊩ₛ Γ → w ⊩ A

  -- Lemma: assumptions are valid (just a lookup).

  ⦅_⦆ₓ : A ∈ Γ → Γ ⊧ A
  ⦅ zero ⦆ₓ    (ρ ∙ a) = a
  ⦅ suc x ⦆ₓ (ρ ∙ a) = ⦅ x ⦆ₓ ρ

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
  ⦅ ` x ⦆   ρ = ⦅ x ⦆ₓ ρ
  ⦅ t ∙ u ⦆ ρ = ⦅ t ⦆ ρ refl (⦅ u ⦆ ρ)
  ⦅ abs t ⦆ ρ = λ η a → ⦅ t ⦆ (monₛ η ρ ∙ a)

module PeirceNotDerivable (X Y : Atom) (X≠Y : X ≢ Y) where
  open RefutePeirce X Y X≠Y
  open Soundness record{ S }

  peirceFalse : ε ⊢ Peirce X Y → ⊥
  peirceFalse t = refute (⦅ t ⦆ ε)
