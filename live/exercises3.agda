{-# OPTIONS --allow-unsolved-metas #-}

module exercises3 where

-- Propositions as types: simple exercises for lecture 3.
-- Same style as test5.agda, but each one is a few symbols.
-- Fill the holes (C-c C-l to load, C-c C-, to see the goal, C-c C-space to
-- give a term, C-c C-c to split on a variable).  Solutions: exercises3-sol.agda

------------------------------------------------------------------------
-- Implication: a proof of P → Q is a function
------------------------------------------------------------------------

-- P ⇒ P
ex1 : {P : Set} → P → P
ex1 x = {!!}

-- P ⇒ Q ⇒ P
ex2 : {P Q : Set} → P → Q → P
ex2 x y = {!!}

-- modus ponens
ex3 : {P Q : Set} → P → (P → Q) → Q
ex3 x f = {!!}

-- transitivity of ⇒ : composition of functions
ex4 : {P Q R : Set} → (P → Q) → (Q → R) → P → R
ex4 f g x = {!!}

-- swapping two hypotheses
ex5 : {P Q R : Set} → (P → Q → R) → Q → P → R
ex5 f y x = {!!}

-- a hypothesis used twice
ex6 : {P Q : Set} → (P → P → Q) → P → Q
ex6 f x = {!!}

------------------------------------------------------------------------
-- Negation: ¬ P is P → ⊥
------------------------------------------------------------------------

data ⊥ : Set where

¬ : Set → Set
¬ P = P → ⊥

-- from ⊥ everything follows: pattern matching with no cases
ex7 : {P : Set} → ⊥ → P
ex7 ()

-- P ⇒ ¬ ¬ P
ex8 : {P : Set} → P → ¬ (¬ P)
ex8 x k = {!!}

-- contraposition
ex9 : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
ex9 f k x = {!!}

-- three negations are as good as one
ex10 : {P : Set} → ¬ (¬ (¬ P)) → ¬ P
ex10 k x = {!!}

-- ¬ (P ∧ ¬ P), with ∧ as two hypotheses
ex11 : {P : Set} → P → ¬ P → ⊥
ex11 x k = {!!}

------------------------------------------------------------------------
-- Conjunction: a pair.  Disjunction: inl or inr
------------------------------------------------------------------------

record _×_ (P Q : Set) : Set where
  constructor _,_
  field
    fst : P
    snd : Q

open _×_

data _+_ (P Q : Set) : Set where
  inl : P → P + Q
  inr : Q → P + Q

-- P ∧ Q ⇒ Q ∧ P
ex12 : {P Q : Set} → P × Q → Q × P
ex12 (x , y) = {!!}

-- P ∧ Q ⇒ P
ex13 : {P Q : Set} → P × Q → P
ex13 (x , y) = {!!}

-- currying: (P ∧ Q ⇒ R) ⇒ (P ⇒ Q ⇒ R), and back
ex14 : {P Q R : Set} → (P × Q → R) → P → Q → R
ex14 f x y = {!!}

ex15 : {P Q R : Set} → (P → Q → R) → P × Q → R
ex15 f (x , y) = {!!}

-- P ⇒ P ∨ Q
ex16 : {P Q : Set} → P → P + Q
ex16 x = {!!}

-- P ∨ Q ⇒ Q ∨ P : a proof by cases
ex17 : {P Q : Set} → P + Q → Q + P
ex17 (inl x) = {!!}
ex17 (inr y) = {!!}

-- (P ⇒ R) ∧ (Q ⇒ R) ⇒ (P ∨ Q ⇒ R)
ex18 : {P Q R : Set} → (P → R) × (Q → R) → P + Q → R
ex18 (f , g) (inl x) = {!!}
ex18 (f , g) (inr y) = {!!}

-- de Morgan: ¬ (P ∨ Q) ⇒ ¬ P ∧ ¬ Q
ex19 : {P Q : Set} → ¬ (P + Q) → ¬ P × ¬ Q
ex19 k = {!!}

-- distributivity
ex20 : {P Q R : Set} → P × (Q + R) → (P × Q) + (P × R)
ex20 (x , inl y) = {!!}
ex20 (x , inr z) = {!!}

-- What about the converses?  ¬ P ∧ ¬ Q ⇒ ¬ (P ∨ Q) is fine.
-- ¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q, and ¬ ¬ P ⇒ P, cannot be proved: a proof of
-- ¬ P + ¬ Q would have to say which one, and we have nothing to decide it with.
