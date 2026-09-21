module peirce where

{-

 In deduction.agda we presented minimal logic on => : the two axioms K and S,
 and modus ponens.  Everything we derived there was derivable.

 How do we show that something is NOT derivable?

 We build a MODEL: an interpretation of the formulae which
   -validates the axioms K and S,
   -is preserved by modus ponens,
 and in which the formula we are interested in is FALSE.  Soundness
 (proved by induction on derivations) then turns a derivation into an
 element of the empty type.

 The formula we take is PEIRCE'S LAW

          ((A => B) => A) => A

 It is a tautology for the classical truth tables -- we check this in
 PART 2 -- so no interpretation in {false,true} can work.  Instead we
 interpret a formula, not by a truth value, but by a MONOTONE PREDICATE
 on the poset with two elements

          w0 <= w1

 One should read w0 <= w1 as "w1 is a later stage of knowledge than w0",
 and "X is forced at w" as "X is known at stage w".  Monotone: what is
 known at w0 is still known at w1.

 The point is the interpretation of implication: X => Y is forced at w
 when, at EVERY later stage u, X forced at u implies Y forced at u.
 So X => Y being forced at w0 is a statement about the FUTURE, and this
 is what makes Peirce's law fail.

-}

-- ------------------------------------------------------------
-- repeated from deduction.agda
-- ------------------------------------------------------------

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

data list (A : Set) : Set where
 nil  : list A
 cons : A -> list A -> list A

data ⊥ : Set where

efq : {A : Set} -> ⊥ -> A
efq ()

record ⊤ : Set where
 constructor tt

-- we shall also need conjunction, to interpret a context
record _∧_ (A B : Set) : Set where
 constructor pair
 field
  fst : A
  snd : B

open _∧_

data Form : Set where
 imply : Form -> Form -> Form
 atom  : Nat -> Form

context : Set
context = list Form

infixr 10 _=>_
_=>_ : Form -> Form -> Form
X => Y = imply X Y

infixr 10 _,_
_,_ : context -> Form -> context
G , X = cons X G

data isIn : context -> Form -> Set where
 zero : {X : Form} -> {G : context} -> isIn (G , X) X
 suc  : {X Y : Form} -> {G : context} -> isIn G X -> isIn (G , Y) X

infixr 6 _⊢_

data _⊢_ : context -> Form -> Set where
 var : {X : Form} -> {G : context} -> isIn G X -> G ⊢ X
 axK : {X Y : Form} -> {G : context} -> G ⊢ X => (Y => X)
 axS : {X Y Z : Form} -> {G : context} -> G ⊢ (X => (Y => Z)) => ((X => Y) => (X => Z))
 mp  : {Y X : Form} -> {G : context} ->
       G ⊢ Y => X ->
       G ⊢ Y ->
       -------------
       G ⊢ X

-- ------------------------------------------------------------
-- ABSOLUTE derivability
--
-- A formula is absolutely derivable when it can be deduced from NO
-- hypothesis at all.  We can define this DIRECTLY, by an inductive
-- definition which is the one of _⊢_ with the rule var removed --
-- there is then no context left, and Deriv is indexed by a formula
-- only.  This is the system of Hilbert.
-- ------------------------------------------------------------

data Deriv : Form -> Set where
 K  : {X Y : Form} -> Deriv (X => (Y => X))
 S  : {X Y Z : Form} -> Deriv ((X => (Y => Z)) => ((X => Y) => (X => Z)))
 MP : {Y X : Form} ->
      Deriv (Y => X) ->
      Deriv Y ->
      -------------
      Deriv X

-- negation, at the level of Agda
not : Set -> Set
not A = A -> ⊥

-- for instance, the identity, as in dedlem1 of deduction.agda
derivId : (X : Form) -> Deriv (X => X)
derivId X = MP (MP S (K {Y = X => X})) (K {Y = X})

-- ------------------------------------------------------------
-- Deriv X  <->  nil ⊢ X
--
-- Both directions are a plain induction on the derivation.
-- ------------------------------------------------------------

-- from left to right: a hypothesis-free derivation can be read in ANY
-- context (so this direction also gives weakening for free)
derivToHil : {G : context} -> {X : Form} -> Deriv X -> G ⊢ X
derivToHil  K         = axK
derivToHil  S         = axS
derivToHil (MP d d1)  = mp (derivToHil d) (derivToHil d1)

-- from right to left: the case var cannot occur, since isIn nil X is
-- empty -- no position in the empty list.  Agda checks this, and the
-- case is written ()
hilToDeriv : {X : Form} -> nil ⊢ X -> Deriv X
hilToDeriv (var ())
hilToDeriv  axK         = K
hilToDeriv  axS         = S
hilToDeriv (mp d d1)    = MP (hilToDeriv d) (hilToDeriv d1)

-- the equivalence
derivIff : (X : Form) -> (Deriv X -> nil ⊢ X) ∧ (nil ⊢ X -> Deriv X)
derivIff X = pair derivToHil hilToDeriv

-- ------------------------------------------------------------
-- The two translations are in fact INVERSE to each other: they do
-- not merely preserve derivability, they are a bijection between
-- the derivation trees of Deriv X and those of nil ⊢ X.
-- ------------------------------------------------------------

data Id (A : Set) : A -> A -> Set where
 refl : (a : A) -> Id A a a

cong2 : {A B C : Set} -> (f : A -> B -> C) ->
        {a a' : A} -> {b b' : B} ->
        Id A a a' -> Id B b b' -> Id C (f a b) (f a' b')
cong2 f (refl a) (refl b) = refl (f a b)

roundDeriv : {X : Form} -> (d : Deriv X) ->
             Id (Deriv X) (hilToDeriv (derivToHil d)) d
roundDeriv  K         = refl K
roundDeriv  S         = refl S
roundDeriv (MP d d1)  = cong2 MP (roundDeriv d) (roundDeriv d1)

roundHil : {X : Form} -> (d : nil ⊢ X) ->
           Id (nil ⊢ X) (derivToHil (hilToDeriv d)) d
roundHil (var ())
roundHil  axK        = refl axK
roundHil  axS        = refl axS
roundHil (mp d d1)   = cong2 mp (roundHil d) (roundHil d1)

-- ============================================================
-- PART 1.  The formulae we want to refute
-- ============================================================

A B : Form
A = atom zero
B = atom (suc zero)

-- Peirce's law
peirce : Form
peirce = ((A => B) => A) => A

-- another classical law of the implicational fragment
peirce2 : Form
peirce2 = ((A => B) => B) => ((B => A) => A)

-- ============================================================
-- PART 2.  The simplest model: the Boolean truth tables
--
-- A model is an interpretation of the formulae which validates K and
-- S and is preserved by MP.  The simplest one interprets a formula by
-- a truth value, implication being given by its truth table.
--
-- It suffices to show that an ATOM is not derivable: interpret every
-- atom by false.
--
-- But it will NOT suffice for Peirce's law, and we prove this too:
-- peirce is true for EVERY Boolean interpretation (peirceTrue below).
-- This is why we shall need a second, finer model.
-- ============================================================

data Bool : Set where
 false true : Bool

-- the truth table of implication
impB : Bool -> Bool -> Bool
impB false y = true
impB true  y = y

-- a Boolean read as a proposition
True : Bool -> Set
True false = ⊥
True true  = ⊤

-- the value of a formula, by recursion on the formula
evalB : (Nat -> Bool) -> Form -> Bool
evalB v (atom n)     = v n
evalB v (imply X Y)  = impB (evalB v X) (evalB v Y)

-- the two axioms are tautologies, and MP preserves truth:
-- all three are checked by trying the finitely many truth values
lemK : (a b : Bool) -> True (impB a (impB b a))
lemK false  b     = tt
lemK true  false  = tt
lemK true  true   = tt

lemS : (a b c : Bool) -> True (impB (impB a (impB b c)) (impB (impB a b) (impB a c)))
lemS false  b      c     = tt
lemS true   false  c     = tt
lemS true   true   false = tt
lemS true   true   true  = tt

lemMP : (a b : Bool) -> True (impB a b) -> True a -> True b
lemMP false  b p q = efq q
lemMP true   b p q = p

-- soundness, by induction on the derivation: one case per constructor
soundB : (v : Nat -> Bool) -> {X : Form} -> Deriv X -> True (evalB v X)
soundB v (K {X} {Y})     = lemK (evalB v X) (evalB v Y)
soundB v (S {X} {Y} {Z}) = lemS (evalB v X) (evalB v Y) (evalB v Z)
soundB v (MP {Y} {X} d d1) =
  lemMP (evalB v Y) (evalB v X) (soundB v d) (soundB v d1)

-- interpret every atom by false
vFalse : Nat -> Bool
vFalse n = false

-- hence no atom is derivable
-- (evalB vFalse (atom n) is false, and True false is the empty type)
notAtom : (n : Nat) -> not (Deriv (atom n))
notAtom n d = soundB vFalse d

-- Peirce's law, on the other hand, is a classical TAUTOLOGY: its
-- value is true whatever the values of the two atoms
lemPeirce : (a b : Bool) -> True (impB (impB (impB a b) a) a)
lemPeirce false  b     = tt
lemPeirce true   false = tt
lemPeirce true   true  = tt

peirceTrue : (v : Nat -> Bool) -> True (evalB v peirce)
peirceTrue v = lemPeirce (v zero) (v (suc zero))

-- so NO Boolean interpretation refutes peirce, and we must look for
-- a model of another kind: this is PART 3 onwards

-- ============================================================
-- PART 3.  The poset  w0 <= w1
-- ============================================================

data World : Set where
 w0 w1 : World

-- the order, defined by RECURSION, so that it computes
-- (as le did in deduction.agda: ⊤ and ⊥ instead of a data type)
infix 8 _≤_
_≤_ : World -> World -> Set
w0 ≤ v  = ⊤
w1 ≤ w0 = ⊥
w1 ≤ w1 = ⊤

leRefl : (w : World) -> w ≤ w
leRefl w0 = tt
leRefl w1 = tt

leTrans : (u v z : World) -> u ≤ v -> v ≤ z -> u ≤ z
leTrans w0  v   z p q = tt
leTrans w1 w0   z p q = efq p
leTrans w1 w1 w0  p q = efq q
leTrans w1 w1 w1  p q = tt

-- ============================================================
-- PART 4.  The monotone predicates on this poset
--
-- A monotone predicate P satisfies  P w0 -> P w1,  so there are
-- exactly THREE of them, and we can list them:
--
--    never   false at w0, false at w1
--    half    false at w0, true  at w1
--    always  true  at w0, true  at w1
--
-- (the missing fourth combination, true at w0 and false at w1, is
--  the one which is not monotone)
--
-- Listing them keeps everything in Set: an interpretation of the
-- atoms is then simply a function  Nat -> Val.
-- ============================================================

data Val : Set where
 never half always : Val

holds : Val -> World -> Set
holds never   w  = ⊥
holds half   w0  = ⊥
holds half   w1  = ⊤
holds always  w  = ⊤

-- each of the three is indeed monotone
holdsMono : (a : Val) -> (u v : World) -> u ≤ v -> holds a u -> holds a v
holdsMono never    u  v  p h = efq h
holdsMono half    w0  v  p h = efq h
holdsMono half    w1 w0  p h = efq p
holdsMono half    w1 w1  p h = tt
holdsMono always   u  v  p h = tt

-- ============================================================
-- PART 5.  Forcing
--
-- Given an interpretation V of the atoms we define, by recursion on
-- the formula X, the set  force V w X  of "proofs that X is known at
-- stage w".  The clause for implication is the one of Kripke:
-- quantification over all LATER stages.
-- ============================================================

force : (Nat -> Val) -> World -> Form -> Set
force V w (atom n)    = holds (V n) w
force V w (imply X Y) = (u : World) -> w ≤ u -> force V u X -> force V u Y

-- forcing is monotone for EVERY formula, by induction on the formula
-- (for an implication there is nothing to do but compose with leTrans:
--  a later stage of a later stage is a later stage)
mono : (V : Nat -> Val) -> (X : Form) -> (u v : World) ->
       u ≤ v -> force V u X -> force V v X
mono V (atom n)     u v p h = holdsMono (V n) u v p h
mono V (imply X Y)  u v p h = \ z q hx -> h z (leTrans u v z p q) hx

-- a context is forced when all its formulae are
forceC : (Nat -> Val) -> World -> context -> Set
forceC V w  nil        = ⊤
forceC V w (cons X G)  = force V w X ∧ forceC V w G

-- reading a hypothesis out of a forced context
lookupC : (V : Nat -> Val) -> {G : context} -> {X : Form} ->
          isIn G X -> (w : World) -> forceC V w G -> force V w X
lookupC V  zero    w g = fst g
lookupC V (suc i)  w g = lookupC V i w (snd g)

-- ============================================================
-- PART 6.  Soundness
--
-- by induction on the derivation: exactly one case per constructor
-- of _⊢_ , as for dedthm in deduction.agda
-- ============================================================

sound : (V : Nat -> Val) -> {G : context} -> {X : Form} ->
        G ⊢ X ->
        (w : World) -> forceC V w G -> force V w X

sound V (var i) w g = lookupC V i w g

-- K: keep hx from stage u to the later stage v -- this is where
-- monotonicity of forcing is used
sound V (axK {X} {Y}) w g = \ u p hx v q hy -> mono V X u v q hx

-- S: at stage z we have f at u, g at v and hx at z, with u <= v <= z
sound V (axS {X} {Y} {Z}) w g =
  \ u p f v q h z r hx -> f z (leTrans u v z q r) hx z (leRefl z) (h z r hx)

-- modus ponens: use the premise at the PRESENT stage, i.e. at w itself
sound V (mp d d1) w g = sound V d w g w (leRefl w) (sound V d1 w g)

-- ============================================================
-- PART 7.  A warm-up: atom 0 => atom 1 is not derivable
--
-- Interpret atom 0 by always and every other atom by never.  Then
-- atom 0 is forced at w0 and atom 1 is not, so atom 0 => atom 1 is
-- not forced at w0.  (Here one world would already be enough: this
-- is just the classical truth table.)
-- ============================================================

V0 : Nat -> Val
V0  zero    = always
V0 (suc n)  = never

notImp : not (Deriv (atom zero => atom (suc zero)))
notImp d = sound V0 (derivToHil d) w0 tt w0 tt tt

-- ============================================================
-- PART 8.  Peirce's law
--
-- Now we really use the two worlds.  Take
--
--     A = atom 0   interpreted by half    (unknown at w0, known at w1)
--     B = atom 1   interpreted by never
--
-- so that A => B is forced NOWHERE: at w0 it fails because of the
-- later stage w1, where A is known and B is not; at w1 it fails at w1.
--
-- Hence  (A => B) => A  is forced at w0 VACUOUSLY, at both stages.
-- But A itself is not forced at w0.  So Peirce's law is not forced
-- at w0, and by soundness it has no derivation.
-- ============================================================

V1 : Nat -> Val
V1  zero    = half
V1 (suc n)  = never

-- the premise of Peirce's law IS forced at w0
-- at stage w0: from f we would get B known at w1, which is absurd
-- at stage w1: nothing to prove, A is known at w1
premise : force V1 w0 ((A => B) => A)
premise w0 p f = efq (f w1 tt tt)
premise w1 p f = tt

-- but the conclusion A is not forced at w0, so Peirce's law has
-- no derivation at all: this is the statement  not (Deriv peirce)
notPeirce : not (Deriv peirce)
notPeirce d = sound V1 (derivToHil d) w0 tt w0 tt premise

{-

 Remarks

 The model also refutes the other classical laws of minimal logic, for
 instance  ((A => B) => B) => ((B => A) => A)  -- see below -- and, once
 negation is added, the law of excluded middle: at w0 neither A nor its
 negation is known.

 Note what soundness gives us: not merely that the axioms K and S do not
 SUFFICE, but that no derivation whatsoever exists.  A derivation would
 be a finite tree, and induction on that tree produces an element of ⊥.

 The Boolean model of PART 2 is the special case of this one where the
 atoms are given values in never / always only: such a value is forced
 at w0 exactly when it is forced at w1, the quantification over later
 stages becomes vacuous, and forcing reduces to the truth tables.  The
 value half, which distinguishes the two stages, is the whole point.

 Note also that the model is finite: forcing at a given world is decidable,
 so this argument could be turned into an algorithm deciding derivability
 for formulae built from two atoms in this fragment.

 Conversely, Peirce's law added as an axiom scheme to K and S gives exactly
 classical implicational logic; the derivation of dedthm in deduction.agda
 goes through unchanged, since it only inspects var, axK, axS and mp.

-}

-- a second classical law, refuted by the same interpretation V1
-- A => B is forced nowhere, so (A => B) => B is forced at w0 vacuously
-- B is forced nowhere either, so B => A is forced at w0
-- and applying the conclusion to it would give A at w0, which is absurd
premise2 : force V1 w0 ((A => B) => B)
premise2 w0 p f = efq (f w1 tt tt)
premise2 w1 p f = efq (f w1 tt tt)

notPeirce2 : not (Deriv peirce2)
notPeirce2 d = sound V1 (derivToHil d) w0 tt w0 tt premise2 w0 tt (\ u q hb -> efq hb)
