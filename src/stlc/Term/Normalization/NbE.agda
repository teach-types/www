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

module Term.Normalization.NbE where

open import Prelude hiding (head)
open import Term renaming (Term to _⊢_)
open import Term.Weakening renaming (Wk to infix 4 _≤_; lookup to weakₓ)
open import Term.KripkeModel

private
  variable
    Γ Δ Φ : Context
    α : BaseTy
    a b c : Ty
    x : a ∈ Γ
    t t' t'' u u' : Γ ⊢ a
    ρ : Γ ≤ Δ

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

  -- Normal spines

  infix 4 _∣_⊢ₙ_
  data _∣_⊢ₙ_ (Γ : Context) : (a : Ty) (c : Ty) → Set where
    []  : Γ ∣ c ⊢ₙ c
    _∷_ : (t : Γ ⊢ₙ a) (s : Γ ∣ b ⊢ₙ c) → Γ ∣ a ⇒ b ⊢ₙ c

  private
    variable
      s : Γ ∣ a ⊢ₙ c

  snoc : (s : Γ ∣ a ⊢ₙ b ⇒ c) (n : Γ ⊢ₙ b) → Γ ∣ a ⊢ₙ c
  snoc []      n = n ∷ []
  snoc (m ∷ s) n = m ∷ snoc s n

  record NeSpine (Γ : Context) (c : Ty) : Set where
    field
      {ty} : Ty
      head : ty ∈ Γ
      spine : Γ ∣ ty ⊢ₙ c
  open NeSpine using (head; spine)

  neSpine : Γ ⊢ᵤ c → NeSpine Γ c
  neSpine (var x) = record{ head = x; spine = [] }
  neSpine (app u n) with neSpine u
  ... | record{ head = x; spine = s} = record{ head = x; spine = snoc s n}

  -- Application: there is no closed normal term of the Peirce type.
  noClosedNeutral : ε ⊢ᵤ a → ⊥
  noClosedNeutral (var ())
  noClosedNeutral (app u _) = noClosedNeutral u

  private
    A = ` "A"
    B = ` "B"

  -- Lemma: we can't derive A ⇒ B from just (A ⇒ B) ⇒ A.

  lemma : ε ∙ (A ⇒ B) ⇒ A ⊢ₙ A ⇒ B → ⊥
  lemma (ne u) with neSpine u
  ... | record { head = zero ; spine = t ∷ () }
  lemma (abs (ne u)) with neSpine u
  ... | record { head = suc zero ; spine = n ∷ () }

  -- The Peirce formula has no normal derivation.

  noPeirce : ε ⊢ₙ ((A ⇒ B) ⇒ A) ⇒ A → ⊥
  noPeirce (ne u) = noClosedNeutral u
  noPeirce (abs (ne u)) with neSpine u
  ... | record { head = zero ; spine = n ∷ [] } = lemma n


------------------------------------------------------------------------
-- Normalization by evaluation.

-- We instantiate our generic soundness theorem to the Kripke model
-- where worlds are contexts under the preorder of weakening
-- and forcing atoms A in a world Γ is witnessed by a neutral derivation Γ ⊢ᵤ A.

module NbEStructure where
  World = Context
  open Term.Weakening public using () renaming (Wk to _≤_; idW to refl; compWW to trans)
  open NormalForms public using (_⊢ᵤ_) renaming (weakᵤ to monₐ)

  _⊩ₐ_ : World → BaseTy → Set
  Γ ⊩ₐ X = Γ ⊢ᵤ ` X

module NbE where

  s : Kripke
  s = record{ NbEStructure }

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
  ⊩ₛid {Γ = ε} = ε
  ⊩ₛid {Γ = Γ ∙ a} = monₛ (skip idW) (⊩ₛid {Γ = Γ}) ∙ reflect {a = a} (var zero)

  -- For each derivation there is also a normal one.
  -- This is now just evaluation (soundness) in the reflected identity environment
  -- followed by reification.
  norm : Γ ⊢ a → Γ ⊢ₙ a
  norm t  = reify (⦅ t ⦆ ⊩ₛid)
