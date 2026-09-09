-- This is a simple example which illustrates the use of propositions as types
-- and representation of ideas of Gentzen for natural deduction in lambda calculus

-- modus ponens is application

-- we also use Set both as a type of types and of propositions

-- we represent the true proposition ⊤ as a data type having one constructor and the false proposition ⊥
-- having no constructor

{-# OPTIONS --allow-unsolved-metas #-}

module euclidean where

open import Agda.Primitive renaming(Set to Type)

symmetric : (X : Type) → (X → X → Type) → Type
symmetric X R = (a b : X) → R a b → R b a

-- (a : X) → (b : X) → R a b → R b a

reflexive : (X : Type) → (X → X → Type) → Type
reflexive X R = (x : X) → R x x

transitive : (X : Type) → (X → X → Type) → Type
transitive X R = (a b c : X) → R a b → R b c → R a c

euclidean : (X : Type) → (X → X → Type) → Type
euclidean X R = (a b c : X) → R a b → R a c → R b c

theorem1 : (A : Type) → (Eq : A → A → Type) → euclidean A Eq → reflexive A Eq → symmetric A Eq
theorem1 A Eq eucl refl a b Eab = {!!} -- eucl a b a Eab (refl a)

-- not that symmetric has been silently unfolded
-- this is a special feature of Agda

-- this is also called the "Poincare Principle"
-- here is a famous example from Leibniz: the statement 2 + 2 = 4 is analytic

data Nat : Type where
 zero : Nat
 succ : Nat → Nat

-- one : Nat
one = succ zero
two = succ one
three = succ two
four = succ three

add : Nat → Nat → Nat
add x zero = x
add x (succ y) = succ (add x y)

-- what is the normal form of add two two and the normal form of four?



theorem2 : (A : Type) → (Eq : A → A → Type) → euclidean A Eq → reflexive A Eq → transitive A Eq
theorem2 A Eq eucl refl a b c Eab Ebc = {!!} -- eucl b a c (theorem1 A Eq eucl refl a b Eab) Ebc

-- counter-example: a relation can be euclidean and not symmetric if it is not reflexive

data CA : Type where
 Ca Cb : CA

data ⊥ : Type where

data ⊤ : Type where
 tt : ⊤

--  relation containing only (Ca, Cb) and (Cb, Cb)
--  in set theory CA = {Ca, Cb} and CEq = { (Ca,Cb), (Cb,Cb) }

CEq : CA → CA → Type
CEq Ca Ca = ⊥
CEq Ca Cb = ⊤
CEq Cb Ca = ⊥
CEq Cb Cb = ⊤

-- we have then 7 cases to consider

remark1 : euclidean CA CEq
remark1 Ca Ca c () CEac
remark1 Ca Cb Ca CEab ()
remark1 Ca Cb Cb CEab CEac = tt
remark1 Cb Ca Ca () CEac
remark1 Cb Ca Cb () CEac
remark1 Cb Cb Ca CEab ()
remark1 Cb Cb Cb CEab CEac = tt
