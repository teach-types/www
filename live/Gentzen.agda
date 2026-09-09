{-# OPTIONS --allow-unsolved-metas #-}

module Gentzen where

open import Agda.Primitive renaming (Set to Type)

record Σ (A : Type) (B : A → Type) : Type where
 constructor _,_          -- : (a : A) → B a → Σ A B
 field
  fst : A
  snd : B fst

open Σ

_×_ : Type → Type → Type
A × B = Σ A (λ _ → B)

infixr 5 _×_

infixr 5 _,_

data _+_ (A B : Type) : Type where
 inl : A → A + B
 inr : B → A + B

+-elim : {A B C : Type} → (A → C) → (B → C) → A + B → C
+-elim f g (inl x) = f x
+-elim f g (inr y) = g y

-- one simple example
-- in Fitch's notation, we have two boxes, corresponding to lambda abstraction

ex1 : {A B C : Type} → (A × B) + (A × C) → A × (B + C)
ex1 = +-elim (λ z → fst z , inl (snd z)) (λ z → fst z , inr (snd z))

-- notation with pattern-matching

pex1 : {A B C : Type} → (A × B) + (A × C) → A × (B + C)
pex1 (inl (x , y)) = (x , inl y)
pex1 (inr (x , y)) = (x , inr y)


-- but actually, we have a -stronger- form of the elimination principle
-- which cannot be formulated in propositional/first-order logic
-- it really needs propositions as types

elim-+ : {A B : Type} → (C : A + B → Type) → ((x : A) → C (inl x)) → ((y : B) → C (inr y)) → (z : A + B) → C z
elim-+ C f g (inl x) = f x
elim-+ C f g (inr y) = g y

data _≡_ {A : Type} (x : A) : A → Type where
 refl : x ≡ x

ex2 : {A B : Type} → (z : A + B) → Σ A (λ x → z ≡ inl x) + Σ B (λ y → z ≡ inr y)
ex2 {A} {B} = elim-+ (λ z → Σ A (λ x → z ≡ inl x) + Σ B (λ y → z ≡ inr y)) (λ x → inl (x , refl)) λ y → inr (y , refl)

-- pattern-matching notation

pex2 : {A B : Type} → (z : A + B) → Σ A (λ x → z ≡ inl x) + Σ B (λ y → z ≡ inr y)
pex2 (inl x) = inl (x , refl)
pex2 (inr y) = inr (y , refl)


Σ-elim : (A : Type) (B : A → Type) (C : Type) →
         ((x0 : A) → B x0 → C) →
         Σ A B → C
Σ-elim A B C box (a , b) = box a b

-- let us prove the "axiom of choice"

ax-choice : {A B : Type} → {R : A → B → Type} → ((x : A) → Σ B (R x)) → Σ (A → B) (λ f → (x : A) → R x (f x))
ax-choice h = (λ x → fst (h x)) , (λ x → snd (h x))

-- a special case is the following

ex3 : {A B C : Type} → (A → B × C) → ((A → B) × (A → C))
ex3 h = (λ x → fst (h x)) , (λ x → snd (h x))

-- NOTATIONS: Gentzen, Prawitz, Howard, Martin-Löf, Fitch, Jaskowski boxes

domain : (A : Type) (B : A → Type) → A → ((x : A) → B x) → Σ A B
domain A B a p = a , p a


data ⊥ : Type where

¬ : Type  → Type
¬ A = A → ⊥

not-exists : (A : Type) (B : A → Type) → ¬ (Σ A B) → (x : A) → ¬ (B x)
not-exists A B p a ab = p (a , ab)

not-forall : (A : Type) (B : A → Type) → ¬ ((x : A) → B x) → Σ A (λ x → ¬ (B x))
not-forall A B p = {!!}

-- we have seen an argument that (X : Type) → X + ¬ X is not derivable via Turing machines
-- with X = Σ A B expressing that a given Turing machine stops
-- there is another argument using Kripke models or more generally, presheaf models

-- J.-Ph. Bernardy, Patrick Jansson Parametricity

-- Martin Hofmann, Syntax and Semantics of Type Theory

-- Simon Huber, PhD thesis
