-- Normalization by evaluation.
--
-- We use an instance of the Kripke model for STLC
-- where worlds are contexts, future is weakening,
-- and forcing `Γ ⊩ a` at base type `a` in world `Γ`
-- is the set of normal forms of type `a` in context `Γ`.
--
-- The soundness theorem gives us for each term `Γ ⊢ a`
-- a semantic value `Γ ⊩ a`, and a function `reify`
-- defined by induction on `a` turns this into a normal
-- form `Γ ⊢ₙ a` (that is the secret sauce).
-- In combination, we get a function mapping terms to normal forms.

module Lecture8NoPeirce where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as ≡ using (_≢_)

-- Simple types.

BaseTy = String

data Ty : Set where
  `_   : (α : BaseTy) → Ty
  _⇒_  : (t₁ t₂ : Ty) → Ty

infixr 10 `_
infixr  9 _⇒_

-- Typing contexts.

data Context : Set where
  ε   : Context
  _∙_ : (Γ : Context) (a : Ty) → Context

infixl 5 _∙_

private
  variable
    α β : BaseTy
    a b c : Ty
    Γ Δ Φ Ξ : Context

-- De Bruijn indices: a variable points to a type in the context.

data _∈_ (a : Ty) : Context → Set where
  zero : a ∈ (Γ ∙ a)
  suc  : (x : a ∈ Γ) → a ∈ (Γ ∙ b)

-- Well-typed terms of the simply-typed lambda-calculus.

infix 4 _⊢_

data _⊢_ (Γ : Context) : Ty → Set where
  var : (x : a ∈ Γ) → Γ ⊢ a
  abs : (t : Γ ∙ a ⊢ b) → Γ ⊢ a ⇒ b
  app : (t : Γ ⊢ a ⇒ b) (u : Γ ⊢ a) → Γ ⊢ b

private
  variable
    x : a ∈ Γ
    t t' t'' u u' : Γ ⊢ a

------------------------------------------------------------------------
-- Kripke models

-- A Kripke model is characterized by a preorder of worlds and
-- a relation (forcing) monotone in worlds
-- that determines which atoms hold at which world.
record KripkeStructure : Set₁ where
  field
    -- A set of worlds.
    World : Set
    -- A preorder on worlds.
    -- w ≤ w' shall mean w is a future of w'.
    _≤_ : (w w' : World) → Set
    refl : ∀{w} → w ≤ w
    trans : ∀{w₁ w₂ w₃} → w₁ ≤ w₂ → w₂ ≤ w₃ → w₁ ≤ w₃
    -- A forcing relation on atoms.
    _⊩ₐ_ : World → BaseTy → Set
    -- Forcing is monotone: true atoms stay true in any future.
    monₐ : ∀{w w' a} → w ≤ w' → w' ⊩ₐ a → w ⊩ₐ a

module Model (Structure : KripkeStructure) (open KripkeStructure Structure) where

  -- The forcing relation extends forcing for atoms to all formulas.
  -- Implication A ⇒ B shall only hold in world w
  -- if the meta-implication (_⊩ A → _⊩ B) holds not just in w but also
  -- in all of its futures w' ≤ w.
  -- This promotes implications from mere coincidences
  -- to laws of consequence.

  private variable
    w w' : World

  infix 8 _⊩_

  _⊩_ : (w : World) (a : Ty) → Set
  w ⊩ (` α)   = w ⊩ₐ α
  w ⊩ (a ⇒ b) = ∀{w'} → w' ≤ w → w' ⊩ a → w' ⊩ b

  -- The forcing relation stays monotone.
  -- This is proven by induction on the formula.

  mon : ∀{w w' a} (ρ : w ≤ w') (v : w' ⊩ a) → w ⊩ a
  mon {a = ` α  } ρ v = monₐ ρ v
  mon {a = a ⇒ b} ρ f = λ ρ' v → f (trans ρ' ρ) v

------------------------------------------------------------------------
-- Soundness: each derivable formula is valid in each Kripke model

module Soundness (Structure : KripkeStructure) where

  open KripkeStructure Structure
  open Model Structure

  private variable w w' : World

  -- We extend forcing to contexts: each formula in the context is forced.
  data _⊩ₛ_ (w : World) : (Γ : Context) → Set where
    ε   : w ⊩ₛ ε
    _∙_ : (δ : w ⊩ₛ Γ) (v : w ⊩ a) → w ⊩ₛ Γ ∙ a
  infixl 5 _∙_
  infix 4 _⊩ₛ_ _⊧_

  monₛ : (ρ : w ≤ w') (δ : w' ⊩ₛ Γ) → w ⊩ₛ Γ
  monₛ ρ ε = ε
  monₛ ρ (_∙_ {a = a} δ v) = monₛ ρ δ ∙ mon {a = a} ρ v

  -- A sequent Γ ⊢ A is valid in the given Structure
  -- if all worlds that force Γ also force A.

  _⊧_ : (Γ : Context) (a : Ty) → Set
  Γ ⊧ a = ∀{w} → w ⊩ₛ Γ → w ⊩ a

  -- Lemma: assumptions are valid (just a lookup).

  ⦅_⦆ₓ : a ∈ Γ → Γ ⊧ a
  ⦅ zero ⦆ₓ  (ρ ∙ v) = v
  ⦅ suc x ⦆ₓ (ρ ∙ v) = ⦅ x ⦆ₓ ρ

  -- Lemma: application is valid
  apply : Γ ⊧ a ⇒ b → Γ ⊧ a → Γ ⊧ b
  apply f g ρ = f ρ refl (g ρ)

  -- Soundness: all derivable sequents Γ ⊢ A are valid.

  ⦅_⦆ : Γ ⊢ a → Γ ⊧ a
  ⦅ var x ⦆ ρ = ⦅ x ⦆ₓ ρ
  ⦅ app t u ⦆ ρ = ⦅ t ⦆ ρ refl (⦅ u ⦆ ρ)
  ⦅ abs t ⦆ ρ = λ η a → ⦅ t ⦆ (monₛ η ρ ∙ a)

------------------------------------------------------------------------
-- "Weakening": transporting terms to larger contexts

-- ρ : Wk Γ Δ  transports a term living in context Δ to a larger context Γ.
-- The relative order of assumptions in Δ is preserved in Γ;
-- Γ is Δ with additional assumptions inserted anywhere.
--
-- In other words, Δ can be obtained by deleting some assumptions from Γ.
-- This perspective is taken by the constructor names, describing how Δ
-- is stepwise constructed from Γ, by either keeping or skipping assumptions.

data _≤_ : (Γ Δ : Context) → Set where
  done : ε ≤ ε
  skip : (ρ : Γ ≤ Δ) → (Γ ∙ a) ≤ Δ
  keep : (ρ : Γ ≤ Δ) → (Γ ∙ a) ≤ (Δ ∙ a)

private
  variable
    ρ : Γ ≤ Δ

-- If Γ ≤ Δ, then any assumption a ∈ Δ is also in Γ.
-- weakₓ (ρ : Γ ≤ Δ) transport de Bruijn indices a ∈ Δ to those a ∈ Γ.
-- In particular, "skip" increases a de Bruijn index.

weakₓ : Γ ≤ Δ → a ∈ Δ → a ∈ Γ
weakₓ (keep ρ) zero    = zero
weakₓ (keep ρ) (suc x) = suc (weakₓ ρ x)
weakₓ (skip ρ) x       = suc (weakₓ ρ x)

-- wk (ρ : Wk Γ Δ)  transports a term from context Δ to larger context Γ
-- by updating the de Bruijn indices.
-- In particular, it maps a term  t : Term Δ a  to a term  wk ρ t : Term Γ a.

wk : Γ ≤ Δ → Δ ⊢ a → Γ ⊢ a
wk ρ (var x)   = var (weakₓ ρ x)
wk ρ (abs t)   = abs (wk (keep ρ) t)
wk ρ (app t u) = app (wk ρ t) (wk ρ u)

-- Weakening compose, so they form a category with identity idW.

idW : Γ ≤ Γ
idW {Γ = ε}     = done
idW {Γ = Γ ∙ _} = keep idW

-- We write composition in the diagrammatic order, so that
-- wk (compWW ρ ρ') = wk ρ ∘ wk ρ'.

compWW : Γ ≤ Δ → Δ ≤ Φ → Γ ≤ Φ
compWW done     ρ'        = ρ'
compWW (skip ρ) ρ'        = skip (compWW ρ ρ')
compWW (keep ρ) (skip ρ') = skip (compWW ρ ρ')
compWW (keep ρ) (keep ρ') = keep (compWW ρ ρ')

-- Some shorthands for common weakenings and weakening operations.

skip1 : (Γ ∙ a) ≤ Γ
skip1 = skip idW

wk1 : Γ ⊢ b → Γ ∙ a ⊢ b
wk1 = wk skip1

------------------------------------------------------------------------
-- Normal forms

module NormalForms where
  mutual
    infix 4 _⊢ᵤ_ _⊢ₙ_

    -- Variable headed normal forms: never reduce even under further applications.
    -- These are also called neutral.

    data _⊢ᵤ_ (Γ : Context) : (a : Ty) → Set where
      var : (x : a ∈ Γ) → Γ ⊢ᵤ a
      app : (u : Γ ⊢ᵤ a ⇒ b) (n : Γ ⊢ₙ a) → Γ ⊢ᵤ b

    -- Normal forms (unless applied to further arguments).

    data _⊢ₙ_ (Γ : Context) : (a : Ty) → Set where
      -- Neutrals are normal
      ne  : (u : Γ ⊢ᵤ a) → Γ ⊢ₙ a
      abs : (t : Γ ∙ a ⊢ₙ b) → Γ ⊢ₙ a ⇒ b

  -- Normal forms are closed under weakening.
  mutual

    weakᵤ : (ρ : Γ ≤ Δ) (u : Δ ⊢ᵤ a) → Γ ⊢ᵤ a
    weakᵤ ρ (var x)    = var (weakₓ ρ x)
    weakᵤ ρ (app u n)  = app (weakᵤ ρ u) (weakₙ ρ n)

    weakₙ : (ρ : Γ ≤ Δ) (n : Δ ⊢ₙ a) → Γ ⊢ₙ a
    weakₙ ρ (ne u)     = ne (weakᵤ ρ u)
    weakₙ ρ (abs n)    = abs (weakₙ (keep ρ) n)

------------------------------------------------------------------------
-- Normalization by evaluation.

-- We instantiate our generic soundness theorem to the Kripke model
-- where worlds are contexts under the preorder of weakening
-- and forcing atoms A in a world Γ is witnessed by a neutral derivation Γ ⊢ᵤ A.

module NbE where
  open NormalForms using (_⊢ᵤ_; weakᵤ)

  s : KripkeStructure
  s = record
    { World = Context
    ; _≤_   = _≤_
    ; refl  = idW
    ; trans = compWW
    ; _⊩ₐ_  = λ Γ X → Γ ⊢ᵤ (` X)
    ; monₐ  = weakᵤ
    }

  open Model s
  open Soundness s
  open NormalForms

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
    reify : Γ ⊩ a → Γ ⊢ₙ a
    reify {a = ` X}   u = ne u
    reify {a = a ⇒ b} f = abs (reify (f (skip idW) (reflect {a = a} (var zero))))

    reflect : Γ ⊢ᵤ a → Γ ⊩ a
    reflect {a = ` X}   u     = u
    reflect {a = a ⇒ b} u ρ v = reflect (app (weakᵤ ρ u) (reify v))

  -- An identity environment in the model is needed to instantiate the soundness theorem.
  -- It is constructed by reflecting each assumption in Γ, using weakening to make the induction on Γ work.
  ⊩ₛid : Γ ⊩ₛ Γ
  ⊩ₛid {Γ = ε}     = ε
  ⊩ₛid {Γ = Γ ∙ a} = monₛ (skip idW) (⊩ₛid {Γ = Γ}) ∙ reflect {a = a} (var zero)

  -- For each derivation there is also a normal one.
  -- This is now just evaluation (soundness) in the reflected identity environment
  -- followed by reification.
  norm : Γ ⊢ a → Γ ⊢ₙ a
  norm t = reify (⦅ t ⦆ ⊩ₛid)
