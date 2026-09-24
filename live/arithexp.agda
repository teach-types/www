module arithexp where

------------------------------------------------------------------------
-- The same development as arith1.agda, with two differences:
--
--  * "progress" is defined as an -inductive family- instead of being
--    built from Σ and + ; the proofs become shorter to read
--  * at the end, the converse of lem1: a well typed normal form
--    -is- a value (lem2)
--
-- The file is self contained on purpose: it can be read on its own.
--
-- G. Plotkin, The Origins of Structural Operational Semantics
-- B. Pierce, Types and Programming Languages, chapter 8
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

exp0 : Exp
exp0 = if (isZ zero) zero (pred zero)


------------------------------------------------------------------------
-- 2.  Small step semantics
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

test=> : exp0 => if true zero (pred zero)
test=> = =>if =>isZ0


------------------------------------------------------------------------
-- 3.  Many steps
------------------------------------------------------------------------

data _=>*_ : Exp -> Exp -> Set where
 nil  : {e : Exp} -> e =>* e
 cons : {e0 e1 e2 : Exp} -> e0 => e1 -> e1 =>* e2 -> e0 =>* e2

isTrans : {e0 e1 e2 : Exp} -> e0 =>* e1 -> e1 =>* e2 -> e0 =>* e2
isTrans nil        q = q
isTrans (cons x p) q = cons x (isTrans p q)

test=>* : exp0 =>* zero
test=>* = cons (=>if =>isZ0) (cons =>true nil)


------------------------------------------------------------------------
-- 4.  Values
------------------------------------------------------------------------

data isValnat : Exp -> Set where
 isValnat0 : isValnat zero
 isValnatS : {e : Exp} -> isValnat e -> isValnat (suc e)

data isVal : Exp -> Set where
 Valtrue  : isVal true
 Valfalse : isVal false
 Valnat   : {e : Exp} -> isValnat e -> isVal e


------------------------------------------------------------------------
-- 5.  Progress, as an inductive family
--
-- Compare with arith1.agda, where the same notion is written
--    progress e = isVal e + Σ Exp (λ e1 -> e => e1)
-- Here we simply say what a proof of progress e can be.
------------------------------------------------------------------------

data progress : Exp -> Set where
 Val : {e : Exp}    -> isVal e -> progress e
 Red : {e e' : Exp} -> e => e' -> progress e

data ⊥ : Set where

¬ : Set -> Set
¬ A = A -> ⊥

explosion : {A : Set} -> ⊥ -> A
explosion ()

isStuck : Exp -> Set
isStuck e = ¬ (progress e)

-- some expressions are stuck: isZ true is neither a value nor reducible

remark : isStuck (isZ true)
remark (Val (Valnat ()))
remark (Red (=>isZ ()))


------------------------------------------------------------------------
-- 6.  Types
--
-- Types appeared first in -logic-, to prevent the paradoxes:
-- B. Russell, 1901 ---> 1908.
------------------------------------------------------------------------

data Typ : Set where
 nat  : Typ
 bool : Typ

-- we cannot write _:_ , so the judgement e : T is written e ofTyp T

data _ofTyp_ : Exp -> Typ -> Set where

 typet :
   ------------------
   true ofTyp bool

 typef :
   ------------------
   false ofTyp bool

 type0 :
   ------------------
   zero ofTyp nat

 typeS : {e : Exp} -> e ofTyp nat ->
   ---------------------------------
   suc e ofTyp nat

 typep : {e : Exp} -> e ofTyp nat ->
   ---------------------------------
   pred e ofTyp nat

 typeZ : {e : Exp} -> e ofTyp nat ->
   ---------------------------------
   isZ e ofTyp bool

 typeif : {T : Typ} -> {e e0 e1 : Exp} ->
          e ofTyp bool -> e0 ofTyp T -> e1 ofTyp T ->
   ----------------------------------------------------
   if e e0 e1 ofTyp T

exp0N : exp0 ofTyp nat
exp0N = typeif (typeZ type0) type0 (typep type0)


------------------------------------------------------------------------
-- 7.  Uniqueness of typing  (TAPL 8.2.4)
------------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

uniqueness : (e : Exp) -> {T T' : Typ} -> e ofTyp T -> e ofTyp T' -> T ≡ T'
uniqueness true        typet           typet             = refl
uniqueness false       typef           typef             = refl
uniqueness zero        type0           type0             = refl
uniqueness (suc _)     (typeS _)       (typeS _)         = refl
uniqueness (pred _)    (typep _)       (typep _)         = refl
uniqueness (isZ _)     (typeZ _)       (typeZ _)         = refl
uniqueness (if _ e0 _) (typeif _ T0 _) (typeif _ T0' _)  = uniqueness e0 T0 T0'


------------------------------------------------------------------------
-- 8.  Preservation  (TAPL 8.3.3)
------------------------------------------------------------------------

preservation : {e e' : Exp} -> {T : Typ} -> e ofTyp T -> e => e' -> e' ofTyp T

preservation (typeif typet eT0 eT1) =>true  = eT0
preservation (typeif typef eT0 eT1) =>false = eT1
preservation (typeZ type0)          =>isZ0  = typet
preservation (typeZ (typeS eT))     =>isZS  = typef
preservation (typep type0)          =>pred0 = type0
preservation (typep (typeS eT))     =>predS = eT

preservation (typeif eT eT0 eT1) (=>if ee')   = typeif (preservation eT ee') eT0 eT1
preservation (typeS eT)          (=>suc ee')  = typeS (preservation eT ee')
preservation (typeZ eT)          (=>isZ ee')  = typeZ (preservation eT ee')
preservation (typep eT)          (=>pred ee') = typep (preservation eT ee')

-- subject -expansion- is false  (TAPL 8.3.6)

exp1 : Exp
exp1 = if true zero false

remark7 : exp1 => zero
remark7 = =>true

remark8 : ¬ (exp1 ofTyp nat)
remark8 (typeif typet type0 ())


------------------------------------------------------------------------
-- 9.  Canonical forms  (TAPL 8.3.1)
------------------------------------------------------------------------

data isBoolVal : Exp -> Set where
 isTrue  : isBoolVal true
 isFalse : isBoolVal false

canon-bool : {e : Exp} -> e ofTyp bool -> isVal e -> isBoolVal e
canon-bool _  Valtrue  = isTrue
canon-bool _  Valfalse = isFalse
canon-bool () (Valnat isValnat0)
canon-bool () (Valnat (isValnatS _))

canon-nat : {e : Exp} -> e ofTyp nat -> isVal e -> isValnat e
canon-nat () Valtrue
canon-nat () Valfalse
canon-nat _  (Valnat v) = v


------------------------------------------------------------------------
-- 10.  Progress  (TAPL 8.3.2)
------------------------------------------------------------------------

if-val : {u e0 e1 : Exp} -> isBoolVal u -> progress (if u e0 e1)
if-val isTrue  = Red =>true
if-val isFalse = Red =>false

pred-val : {u : Exp} -> isValnat u -> progress (pred u)
pred-val isValnat0     = Red =>pred0
pred-val (isValnatS _) = Red =>predS

isZ-val : {u : Exp} -> isValnat u -> progress (isZ u)
isZ-val isValnat0     = Red =>isZ0
isZ-val (isValnatS _) = Red =>isZS

typeprog-if : {u e0 e1 : Exp} -> u ofTyp bool -> progress u -> progress (if u e0 e1)
typeprog-if uT (Val v) = if-val (canon-bool uT v)
typeprog-if uT (Red x) = Red (=>if x)

typeprog-suc : {u : Exp} -> u ofTyp nat -> progress u -> progress (suc u)
typeprog-suc uT (Val v) = Val (Valnat (isValnatS (canon-nat uT v)))
typeprog-suc uT (Red x) = Red (=>suc x)

typeprog-pred : {u : Exp} -> u ofTyp nat -> progress u -> progress (pred u)
typeprog-pred uT (Val v) = pred-val (canon-nat uT v)
typeprog-pred uT (Red x) = Red (=>pred x)

typeprog-isZ : {u : Exp} -> u ofTyp nat -> progress u -> progress (isZ u)
typeprog-isZ uT (Val v) = isZ-val (canon-nat uT v)
typeprog-isZ uT (Red x) = Red (=>isZ x)

typeprog : {e : Exp} -> {T : Typ} -> e ofTyp T -> progress e
typeprog typet               = Val Valtrue
typeprog typef               = Val Valfalse
typeprog type0               = Val (Valnat isValnat0)
typeprog (typeS eT)          = typeprog-suc eT (typeprog eT)
typeprog (typep eT)          = typeprog-pred eT (typeprog eT)
typeprog (typeZ eT)          = typeprog-isZ eT (typeprog eT)
typeprog (typeif eT eT0 eT1) = typeprog-if eT (typeprog eT)


------------------------------------------------------------------------
-- 11.  Safety = progress + preservation
--
-- "well typed programs cannot go wrong"  (R. Milner, 1978)
--
-- by induction on =>* , that is on the length of the computation;
-- Z. Manna called this computational induction
--   http://www.cs.tau.ac.il/~nachumd/term/MNV.pdf
------------------------------------------------------------------------

theorem : {e e' : Exp} -> {T : Typ} -> e ofTyp T -> e =>* e' -> progress e'
theorem eT nil        = typeprog eT
theorem eT (cons x q) = theorem (preservation eT x) q


------------------------------------------------------------------------
-- 12.  Values and normal forms
--
-- lem1: a value never reduces
-- lem2: the converse, for -well typed- expressions
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

-- if the subexpression is already a value, the whole expression reduces,
-- hence is not normal

if-red : {u e0 e1 : Exp} -> isBoolVal u -> ¬ (=>normal (if u e0 e1))
if-red isTrue  ne = ne =>true
if-red isFalse ne = ne =>false

pred-red : {u : Exp} -> isValnat u -> ¬ (=>normal (pred u))
pred-red isValnat0     ne = ne =>pred0
pred-red (isValnatS _) ne = ne =>predS

isZ-red : {u : Exp} -> isValnat u -> ¬ (=>normal (isZ u))
isZ-red isValnat0     ne = ne =>isZ0
isZ-red (isValnatS _) ne = ne =>isZS

lem2 : {e : Exp} -> {T : Typ} -> e ofTyp T -> =>normal e -> isVal e

lem2 typet ne = Valtrue
lem2 typef ne = Valfalse
lem2 type0 ne = Valnat isValnat0

lem2 (typeS eT) ne =
  Valnat (isValnatS (canon-nat eT (lem2 eT (λ h -> ne (=>suc h)))))

lem2 (typep eT) ne =
  explosion (pred-red (canon-nat eT (lem2 eT (λ h -> ne (=>pred h)))) ne)

lem2 (typeZ eT) ne =
  explosion (isZ-red (canon-nat eT (lem2 eT (λ h -> ne (=>isZ h)))) ne)

lem2 (typeif eT eT0 eT1) ne =
  explosion (if-red (canon-bool eT (lem2 eT (λ h -> ne (=>if h)))) ne)
