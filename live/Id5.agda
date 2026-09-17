module Id5 where

{-

 Lecture 5, first hour: the identity type, and elimination rules

 Andreas covered formation, introduction (refl) and the RESTRICTED
 eliminator subst.  Here we look at what subst cannot say, at the
 general elimination rule, and at the notion of MOTIVE, which is
 common to the elimination rule of EVERY inductive type

-}

data Bool : Set where
 true false : Bool

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

data ⊥ : Set where

efq : {A : Set} -> ⊥ -> A
efq ()

record ⊤ : Set where
 constructor tt

data list (A : Set) : Set where
 nil  : list A
 cons : A -> list A -> list A

-- ------------------------------------------------------------
-- 1.  The identity type
-- ------------------------------------------------------------

-- A is a PARAMETER, the two endpoints are INDICES
-- (this is the formulation of Martin-Lof: refl a chooses both
--  indices to be a)
data Id (A : Set) : A -> A -> Set where
 refl : (a : A) -> Id A a a

-- Another version, the one of the last lecture: the first endpoint
-- is a PARAMETER, so it is fixed, and only the second one is an index
data Id' (A : Set) (a : A) : A -> Set where
 refl' : Id' A a a

-- the two versions are equivalent: from the eliminator of Id' --
-- whose motive keeps the first endpoint fixed -- the general rule of
-- section 3 follows at once.  It is the CONVERSE, deriving the rule
-- of Id' from the general one, which is surprisingly subtle, and we
-- do not do it here

-- congruence, used in the examples below
-- (it is an instance of the elimination rule of section 3)
cong : {A B : Set} -> (f : A -> B) -> {a b : A} -> Id A a b -> Id B (f a) (f b)
cong f (refl a) = refl (f a)

-- ------------------------------------------------------------
-- 2.  Elimination rules and their motive
--
-- Every elimination rule has the same shape:
--   a MOTIVE C, which says what we want to prove, and which may
--     depend on the element being eliminated;
--   one premise per constructor, at the corresponding instance of C;
--   a conclusion C t.
-- ------------------------------------------------------------

BoolRec : (C : Bool -> Set) ->
          C true -> C false ->
          (b : Bool) -> C b
BoolRec C x y  true  = x
BoolRec C x y  false = y

not : Bool -> Bool
not  true = false
not false = true

-- the motive here really depends on b: with a constant motive
-- (the if-then-else of Part 1) this statement cannot be proved
notnot : (b : Bool) -> Id Bool (not (not b)) b
notnot = BoolRec (\ b -> Id Bool (not (not b)) b) (refl true) (refl false)

NatRec : (C : Nat -> Set) ->
         C zero ->
         ((n : Nat) -> C n -> C (suc n)) ->
         (n : Nat) -> C n
NatRec C base step  zero   = base
NatRec C base step (suc n) = step n (NatRec C base step n)

_+_ : Nat -> Nat -> Nat
zero  + n = n
suc m + n = suc (m + n)

-- with a CONSTANT motive this is primitive recursion;
-- with a motive depending on n it is proof by induction
addZero : (n : Nat) -> Id Nat (n + zero) n
addZero = NatRec (\ n -> Id Nat (n + zero) n) (refl zero) (\ n h -> cong suc h)

listRec : {A : Set} -> (C : list A -> Set) ->
          C nil ->
          ((a : A) -> (as : list A) -> C as -> C (cons a as)) ->
          (as : list A) -> C as
listRec C base step  nil        = base
listRec C base step (cons a as) = step a as (listRec C base step as)

length : {A : Set} -> list A -> Nat
length {A} = listRec (\ _ -> Nat) zero (\ a as n -> suc n)

-- binary trees: the constructor branch has TWO recursive arguments,
-- so the step case has TWO induction hypotheses
data Tree (A : Set) : Set where
 leaf   : A -> Tree A
 branch : Tree A -> Tree A -> Tree A

TreeRec : {A : Set} -> (C : Tree A -> Set) ->
          ((a : A) -> C (leaf a)) ->
          ((t1 t2 : Tree A) -> C t1 -> C t2 -> C (branch t1 t2)) ->
          (t : Tree A) -> C t
TreeRec C base step (leaf a)       = base a
TreeRec C base step (branch t1 t2) =
  step t1 t2 (TreeRec C base step t1) (TreeRec C base step t2)

-- an example of a proof by induction on a tree
cong2 : {A B C : Set} -> (f : A -> B -> C) ->
        {a a' : A} -> {b b' : B} ->
        Id A a a' -> Id B b b' -> Id C (f a b) (f a' b')
cong2 f (refl a) (refl b) = refl (f a b)

rev : {A : Set} -> Tree A -> Tree A
rev (leaf a)       = leaf a
rev (branch t1 t2) = branch (rev t2) (rev t1)

revrev : {A : Set} -> (t : Tree A) -> Id (Tree A) t (rev (rev t))
revrev {A} = TreeRec (\ t -> Id (Tree A) t (rev (rev t)))
                     (\ a -> refl (leaf a))
                     (\ t1 t2 h1 h2 -> cong2 branch h1 h2)

-- ------------------------------------------------------------
-- 3.  The same rule for Id: its eliminator is J
--
-- the motive of subst was  C : A -> Set
-- the motive of the elimination rule mentions the two endpoints
-- AND the proof, and the premise is at refl
-- ------------------------------------------------------------

IdRec : {A : Set} -> (C : (x y : A) -> Id A x y -> Set) ->
        (a b : A) -> (p : Id A a b) ->
        ((x : A) -> C x x (refl x)) -> C a b p
IdRec C a a (refl a) d = d a

-- the traditional name of this eliminator is J
J : {A : Set} -> (C : (x y : A) -> Id A x y -> Set) ->
    (a b : A) -> (p : Id A a b) ->
    ((x : A) -> C x x (refl x)) -> C a b p
J = IdRec

-- computation rule:  IdRec C a a (refl a) d = d a   holds by definition
Jcomp : {A : Set} -> (C : (x y : A) -> Id A x y -> Set) ->
        (d : (x : A) -> C x x (refl x)) -> (a : A) ->
        Id (C a a (refl a)) (IdRec C a a (refl a) d) (d a)
Jcomp C d a = refl (d a)

-- ------------------------------------------------------------
-- 4.  subst, the restricted form
--
-- take the motive to ignore the proof: C depends on ONE endpoint.
-- This is the rule Andreas gave, and it is an INSTANCE of J
-- ------------------------------------------------------------

subst : {A : Set} -> (C : A -> Set) -> {a b : A} -> Id A a b -> C a -> C b
subst C {a} {b} p = J (\ x y _ -> C x -> C y) a b p (\ x w -> w)

-- pattern matching gives it directly, with the same computation rule
subst2 : {A : Set} -> (C : A -> Set) -> {a b : A} -> Id A a b -> C a -> C b
subst2 C (refl a) c = c

-- Leibniz: equals may be substituted for equals.  From it:
sym : {A : Set} -> {a b : A} -> Id A a b -> Id A b a
sym {A} {a} p = subst (\ y -> Id A y a) p (refl a)

trans : {A : Set} -> {a b c : A} -> Id A a b -> Id A b c -> Id A a c
trans {A} {a} p q = subst (\ y -> Id A a y) q p

-- cong of section 1 is the instance of subst whose motive is
-- (\ y -> Id B (f a) (f y)), with base case refl (f a)
congSubst : {A B : Set} -> (f : A -> B) -> {a b : A} ->
            Id A a b -> Id B (f a) (f b)
congSubst {A} {B} f {a} p = subst (\ y -> Id B (f a) (f y)) p (refl (f a))

-- the based form: the first endpoint is fixed, so the last premise is
-- a single element instead of a function of x
J' : {A : Set} -> (a b : A) -> (C : (y : A) -> Id A a y -> Set) ->
     (p : Id A a b) -> C a (refl a) -> C b p
J' a a C (refl a) c = c

-- ------------------------------------------------------------
-- 5.  Zero is not one
--
-- Nothing proved so far distinguishes two elements of Nat: subst and
-- J only let us REPLACE equals by equals.  To prove that zero and
-- suc zero are different we define equality of numbers a second
-- time, BY RECURSION, so that it computes
-- ------------------------------------------------------------

eqNat : Nat -> Nat -> Set
eqNat  zero     zero   = ⊤
eqNat  zero    (suc y) = ⊥
eqNat (suc x)   zero   = ⊥
eqNat (suc x)  (suc y) = eqNat x y

eqNatRefl : (x : Nat) -> eqNat x x
eqNatRefl  zero   = tt
eqNatRefl (suc x) = eqNatRefl x

-- Id x y implies eqNat x y: this is subst, with motive (\ z -> eqNat x z)
toEq : (x y : Nat) -> Id Nat x y -> eqNat x y
toEq x y p = subst (\ z -> eqNat x z) p (eqNatRefl x)

-- and conversely, so the two are equivalent
fromEq : (x y : Nat) -> eqNat x y -> Id Nat x y
fromEq  zero     zero   h = refl zero
fromEq  zero    (suc y) h = efq h
fromEq (suc x)   zero   h = efq h
fromEq (suc x)  (suc y) h = cong suc (fromEq x y h)

-- now zero is not one, since eqNat zero (suc zero) COMPUTES to ⊥
zeroNotOne : Id Nat zero (suc zero) -> ⊥
zeroNotOne p = toEq zero (suc zero) p

-- with pattern matching, the same proof is one line: Agda checks that
-- no constructor can produce an element of Id Nat zero (suc zero),
-- and asks for no clause at all
zeroNotOne' : Id Nat zero (suc zero) -> ⊥
zeroNotOne' ()

-- ------------------------------------------------------------
-- 6.  Id is intensional
--
-- Two functions which agree on every argument are not provably
-- equal: this statement can be written down, but it is not provable
-- ------------------------------------------------------------

-- one direction is immediate: equal functions may be applied to the
-- same argument, and cong (Leibniz) does the rest
happly : {A B : Set} -> (f g : A -> B) ->
         Id (A -> B) f g -> (x : A) -> Id B (f x) (g x)
happly f g p x = cong (\ h -> h x) p

-- the CONVERSE is the problem
funExt : Set1
funExt = {A B : Set} -> (f g : A -> B) ->
         ((x : A) -> Id B (f x) (g x)) -> Id (A -> B) f g

-- Similarly for propositional extensionality: if A and B are
-- equivalent propositions, are they equal?  (this one needs a
-- universe to be stated: it is an equality between two elements
-- of Set)

-- These are not consequences of the rules.  One may add them as
-- axioms, at the price of losing the computation of the proofs

-- ------------------------------------------------------------
-- Exercises
-- ------------------------------------------------------------

-- 1. define sym, trans and cong from J instead of subst
-- 2. define J from J', and J' from J
-- 3. prove  (b : Bool) -> Id Bool (not (not b)) b  by pattern
--    matching, and compare with notnot above
-- 4. state and prove, for + defined above,
--       (m n : Nat) -> Id Nat (m + suc n) (suc (m + n))
--    once with NatRec and once by pattern matching
