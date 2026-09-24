module arith1 where

open import Agda.Primitive renaming (Set to Type)

------------------------------------------------------------------------
-- A very small programming language, and what types are for
--
-- G. Plotkin, The Origins of Structural Operational Semantics
--   https://homepages.inf.ed.ac.uk/gdp/publications/Origins_SOS.pdf
-- B. Pierce, Types and Programming Languages, chapter 8
--
-- Everything below is an -indexed inductive family-: the syntax, the
-- one step relation, the typing relation.  A derivation is a term.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- 1.  The syntax
------------------------------------------------------------------------

data Exp : Set where
 true   : Exp
 false  : Exp
 zero   : Exp
 suc    : Exp -> Exp
 if     : Exp -> Exp -> Exp -> Exp
 pred   : Exp -> Exp
 isZ    : Exp -> Exp

-- the expression we shall follow all along

exp0 : Exp
exp0 = if (isZ zero) zero (pred zero)


------------------------------------------------------------------------
-- 2.  Small step semantics:  e => e'  is "e computes to e' in one step"
--
-- Two kinds of rules:
--   computation rules, which do some work,
--   congruence rules, which say -where- the next step may be taken.
------------------------------------------------------------------------

data _=>_ : Exp -> Exp -> Set where

 -- computation

 =>true : {e0 e1 : Exp} ->
   ------------------------
   if true e0 e1 => e0

 =>false : {e0 e1 : Exp} ->
   ------------------------
   if false e0 e1 => e1

 =>isZ0 :
   ------------------------
   isZ zero => true

 =>isZS : {e : Exp} ->
   ------------------------
   isZ (suc e) => false

 =>pred0 :
   ------------------------
   pred zero => zero

 =>predS : {e : Exp} ->
   ------------------------
   pred (suc e) => e

 -- congruence

 =>if : {e e' e0 e1 : Exp} -> e => e' ->
   ------------------------------------
   if e e0 e1 => if e' e0 e1

 =>suc : {e e' : Exp} -> e => e' ->
   ------------------------------------
   suc e => suc e'

 =>isZ : {e e' : Exp} -> e => e' ->
   ------------------------------------
   isZ e => isZ e'

 =>pred : {e e' : Exp} -> e => e' ->
   ------------------------------------
   pred e => pred e'

-- a -proof- of one step is a term built from these constructors

test=> : exp0 => if true zero (pred zero)
test=> = =>if =>isZ0


------------------------------------------------------------------------
-- 3.  Many steps:  the reflexive transitive closure of =>
------------------------------------------------------------------------

data _=>*_ : Exp -> Exp -> Set where
 nil  : {e : Exp} -> e =>* e
 cons : {e0 e1 e2 : Exp} -> e0 => e1 -> e1 =>* e2 -> e0 =>* e2

-- a list of steps; concatenation of lists is transitivity

isTrans : {e0 e1 e2 : Exp} -> e0 =>* e1 -> e1 =>* e2 -> e0 =>* e2
isTrans nil        q = q
isTrans (cons x p) q = cons x (isTrans p q)

oneStep : {e0 e1 : Exp} -> e0 => e1 -> e0 =>* e1
oneStep x = cons x nil

test=>* : exp0 =>* zero
test=>* = cons (=>if =>isZ0) (cons =>true nil)


------------------------------------------------------------------------
-- 4.  The values of this language
--
-- a value of type nat is a numeral, a value of type bool is true or false
------------------------------------------------------------------------

data isValnat : Exp -> Set where
 isValnat0 : isValnat zero
 isValnatS : {e : Exp} -> isValnat e -> isValnat (suc e)

data isVal : Exp -> Set where
 Valtrue  : isVal true
 Valfalse : isVal false
 Valnat   : {e : Exp} -> isValnat e -> isVal e

-- the expressions satisfying isValnat are exactly the numerals

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

encodeN : Nat -> Exp
encodeN zero    = zero
encodeN (suc n) = suc (encodeN n)

encodeVal : (n : Nat) -> isValnat (encodeN n)
encodeVal zero    = isValnat0
encodeVal (suc n) = isValnatS (encodeVal n)

decodeN : {e : Exp} -> isValnat e -> Nat
decodeN isValnat0     = zero
decodeN (isValnatS v) = suc (decodeN v)


------------------------------------------------------------------------
-- 5.  Progress, and terms that are stuck
--
-- To state progress we need a disjunction and an existential quantifier.
------------------------------------------------------------------------

record Σ (A : Type) (B : A -> Type) : Type where
 constructor _,_
 field
  fst : A
  snd : B fst

open Σ

infixr 5 _,_

_×_ : Type -> Type -> Type
A × B = Σ A (λ _ -> B)

infixr 5 _×_

data _+_ (A B : Type) : Type where
 inl : A -> A + B
 inr : B -> A + B

-- "e is a value, or e can take one more step"

progress : Exp -> Set
progress e = isVal e + Σ Exp (λ e1 -> e => e1)

data ⊥ : Set where

¬ : Set -> Set
¬ A = A -> ⊥

explosion : {A : Set} -> ⊥ -> A
explosion ()

isStuck : Exp -> Set
isStuck e = ¬ (progress e)

-- some expressions are stuck: isZ true is neither a value nor reducible

remark : isStuck (isZ true)
remark (inl (Valnat ()))
remark (inr (_ , =>isZ ()))


------------------------------------------------------------------------
-- 6.  Types, to rule the stuck terms out
--
-- Types appeared first in -logic-, to prevent the paradoxes:
-- B. Russell, 1901 ---> 1908.
------------------------------------------------------------------------

data Typ : Set where
 nat  : Typ
 bool : Typ

-- we cannot write _:_ , so the typing judgement e : T is written e :: T

data _::_ : Exp -> Typ -> Set where

 typet :
   ------------------
   true :: bool

 typef :
   ------------------
   false :: bool

 type0 :
   ------------------
   zero :: nat

 typeS : {e : Exp} -> e :: nat ->
   ------------------------------
   suc e :: nat

 typep : {e : Exp} -> e :: nat ->
   ------------------------------
   pred e :: nat

 typeZ : {e : Exp} -> e :: nat ->
   ------------------------------
   isZ e :: bool

 typeif : {T : Typ} -> {e e0 e1 : Exp} ->
          e :: bool -> e0 :: T -> e1 :: T ->
   --------------------------------------------
   if e e0 e1 :: T

-- a derivation of a typing judgement e :: T is a term of this type,
-- written with constructors only

exp0N : exp0 :: nat
exp0N = typeif (typeZ type0) type0 (typep type0)


------------------------------------------------------------------------
-- 7.  Uniqueness of typing  (TAPL 8.2.4)
------------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

uniqueness : (e : Exp) -> {T T' : Typ} -> e :: T -> e :: T' -> T ≡ T'
uniqueness true      typet          typet             = refl
uniqueness false     typef          typef             = refl
uniqueness zero      type0          type0             = refl
uniqueness (suc _)   (typeS _)      (typeS _)         = refl
uniqueness (pred _)  (typep _)      (typep _)         = refl
uniqueness (isZ _)   (typeZ _)      (typeZ _)         = refl
uniqueness (if _ e0 _) (typeif _ T0 _) (typeif _ T0' _) = uniqueness e0 T0 T0'


------------------------------------------------------------------------
-- 8.  Preservation, also called subject reduction  (TAPL 8.3.3)
--
-- one clause per pair (typing rule, reduction rule) that can meet
------------------------------------------------------------------------

preservation : {e e' : Exp} -> {T : Typ} -> e :: T -> e => e' -> e' :: T

preservation (typeif typet eT0 eT1) =>true  = eT0
preservation (typeif typef eT0 eT1) =>false = eT1
preservation (typeZ type0)          =>isZ0  = typet
preservation (typeZ (typeS eT))     =>isZS  = typef
preservation (typep type0)          =>pred0 = type0
preservation (typep (typeS eT))     =>predS = eT

preservation (typeif eT eT0 eT1) (=>if ee') = typeif (preservation eT ee') eT0 eT1
preservation (typeS eT)          (=>suc ee')  = typeS (preservation eT ee')
preservation (typeZ eT)          (=>isZ ee')  = typeZ (preservation eT ee')
preservation (typep eT)          (=>pred ee') = typep (preservation eT ee')

-- the converse, subject -expansion-, is false  (TAPL 8.3.6)

exp1 : Exp
exp1 = if true zero false

remark7 : exp1 => zero
remark7 = =>true

remark8 : ¬ (exp1 :: nat)
remark8 (typeif typet type0 ())


------------------------------------------------------------------------
-- 9.  Canonical forms  (TAPL 8.3.1)
--
-- What a value of a given type can look like.  These two little lemmas
-- are what makes the proof of progress short.
------------------------------------------------------------------------

data isBoolVal : Exp -> Set where
 isTrue  : isBoolVal true
 isFalse : isBoolVal false

canon-bool : {e : Exp} -> e :: bool -> isVal e -> isBoolVal e
canon-bool _  Valtrue  = isTrue
canon-bool _  Valfalse = isFalse
canon-bool () (Valnat isValnat0)
canon-bool () (Valnat (isValnatS _))

canon-nat : {e : Exp} -> e :: nat -> isVal e -> isValnat e
canon-nat () Valtrue
canon-nat () Valfalse
canon-nat _  (Valnat v) = v


------------------------------------------------------------------------
-- 10.  Progress: a well typed expression is a value or reduces  (TAPL 8.3.2)
------------------------------------------------------------------------

-- first, what to do when the subexpression is already a value

if-val : {u e0 e1 : Exp} -> isBoolVal u -> progress (if u e0 e1)
if-val {e0 = e0} isTrue  = inr (e0 , =>true)
if-val {e1 = e1} isFalse = inr (e1 , =>false)

pred-val : {u : Exp} -> isValnat u -> progress (pred u)
pred-val isValnat0         = inr (zero , =>pred0)
pred-val (isValnatS {e} _) = inr (e , =>predS)

isZ-val : {u : Exp} -> isValnat u -> progress (isZ u)
isZ-val isValnat0     = inr (true , =>isZ0)
isZ-val (isValnatS _) = inr (false , =>isZS)

-- then one lemma per construction: either the subexpression moves,
-- or it is a value and canonical forms tells us which one

typeprog-if : {u e0 e1 : Exp} -> u :: bool -> progress u -> progress (if u e0 e1)
typeprog-if uT (inl v)                    = if-val (canon-bool uT v)
typeprog-if {e0 = e0} {e1} uT (inr (u' , x)) = inr (if u' e0 e1 , =>if x)

typeprog-suc : {u : Exp} -> u :: nat -> progress u -> progress (suc u)
typeprog-suc uT (inl v)        = inl (Valnat (isValnatS (canon-nat uT v)))
typeprog-suc uT (inr (u' , x)) = inr (suc u' , =>suc x)

typeprog-pred : {u : Exp} -> u :: nat -> progress u -> progress (pred u)
typeprog-pred uT (inl v)        = pred-val (canon-nat uT v)
typeprog-pred uT (inr (u' , x)) = inr (pred u' , =>pred x)

typeprog-isZ : {u : Exp} -> u :: nat -> progress u -> progress (isZ u)
typeprog-isZ uT (inl v)        = isZ-val (canon-nat uT v)
typeprog-isZ uT (inr (u' , x)) = inr (isZ u' , =>isZ x)

-- progress itself: structural induction on the typing derivation

typeprog : {e : Exp} -> {T : Typ} -> e :: T -> progress e
typeprog typet               = inl Valtrue
typeprog typef               = inl Valfalse
typeprog type0               = inl (Valnat isValnat0)
typeprog (typeS eT)          = typeprog-suc eT (typeprog eT)
typeprog (typep eT)          = typeprog-pred eT (typeprog eT)
typeprog (typeZ eT)          = typeprog-isZ eT (typeprog eT)
typeprog (typeif eT eT0 eT1) = typeprog-if eT (typeprog eT)


------------------------------------------------------------------------
-- 11.  Safety = progress + preservation
--
-- "well typed programs cannot go wrong"  (R. Milner, 1978)
--
-- The proof is by induction on =>* , that is, on the length of the
-- computation; Z. Manna called this computational induction.
--   Manna, Ness, Vuillemin, Inductive methods for proving properties
--   of programs, 1973   http://www.cs.tau.ac.il/~nachumd/term/MNV.pdf
------------------------------------------------------------------------

theorem : {e e' : Exp} -> {T : Typ} -> e :: T -> e =>* e' -> progress e'
theorem eT nil        = typeprog eT
theorem eT (cons x q) = theorem (preservation eT x) q


------------------------------------------------------------------------
-- 12.  Values and normal forms
--
-- A value never reduces.  The converse needs the typing:
-- see lem2 in arithexp.agda
------------------------------------------------------------------------

=>normal : Exp -> Set
=>normal e = {e1 : Exp} -> ¬ (e => e1)

lem0 : {e : Exp} -> isValnat e -> =>normal e
lem0 isValnat0      ()
lem0 (isValnatS ie) (=>suc h) = lem0 ie h

lem1 : {e : Exp} -> isVal e -> =>normal e
lem1 Valtrue    ()
lem1 Valfalse   ()
lem1 (Valnat x) = lem0 x
