module operational where

-- Small step and big step semantics of the language of arith1.agda
--
-- G. Plotkin, The Origins of Structural Operational Semantics
--   https://homepages.inf.ed.ac.uk/gdp/publications/Origins_SOS.pdf
-- G. Kahn, Natural semantics, 1987
--
-- We reuse the syntax Exp, the one step relation => , its closure =>*
-- and the values from arith1.agda, and add the -big step- relation.

open import arith1


------------------------------------------------------------------------
-- 1.  Big step semantics:  e ⇓ v  is "e evaluates to the value v"
--
-- No intermediate state is mentioned.  A derivation of e ⇓ v is the
-- whole computation tree at once, not a sequence of steps.
------------------------------------------------------------------------

data _⇓_ : Exp -> Exp -> Set where

 -- a value evaluates to itself

 vtrue :
   ------------------
   true ⇓ true

 vfalse :
   ------------------
   false ⇓ false

 v0 :
   ------------------
   zero ⇓ zero

 ⇓suc : {e v : Exp} -> e ⇓ v ->
   ------------------------------
   suc e ⇓ suc v

 ⇓isZ0 : {e : Exp} -> e ⇓ zero ->
   ------------------------------
   isZ e ⇓ true

 ⇓isZS : {e v : Exp} -> e ⇓ suc v ->
   ------------------------------------
   isZ e ⇓ false

 ⇓pred0 : {e : Exp} -> e ⇓ zero ->
   ------------------------------
   pred e ⇓ zero

 ⇓predS : {e v : Exp} -> e ⇓ suc v ->
   ------------------------------------
   pred e ⇓ v

 ⇓iftrue : {e e0 e1 v : Exp} -> e ⇓ true -> e0 ⇓ v ->
   ---------------------------------------------------
   if e e0 e1 ⇓ v

 ⇓iffalse : {e e0 e1 v : Exp} -> e ⇓ false -> e1 ⇓ v ->
   ----------------------------------------------------
   if e e0 e1 ⇓ v

-- the same expression as before, evaluated in one derivation tree

test⇓ : exp0 ⇓ zero
test⇓ = ⇓iftrue (⇓isZ0 v0) v0


------------------------------------------------------------------------
-- 2.  Values evaluate to themselves
------------------------------------------------------------------------

⇓valnat : {e : Exp} -> isValnat e -> e ⇓ e
⇓valnat isValnat0     = v0
⇓valnat (isValnatS v) = ⇓suc (⇓valnat v)

⇓val : {e : Exp} -> isVal e -> e ⇓ e
⇓val Valtrue    = vtrue
⇓val Valfalse   = vfalse
⇓val (Valnat v) = ⇓valnat v

-- Warning: without types, the result of ⇓ need not be a value.
-- Indeed  suc true ⇓ suc true  by ⇓suc vtrue, and suc true is not a value.
-- This is the big step counterpart of a stuck term.


------------------------------------------------------------------------
-- 3.  The congruence rules of =>* , which => has and =>* inherits
------------------------------------------------------------------------

=>*suc : {e e' : Exp} -> e =>* e' -> suc e =>* suc e'
=>*suc nil        = nil
=>*suc (cons x p) = cons (=>suc x) (=>*suc p)

=>*pred : {e e' : Exp} -> e =>* e' -> pred e =>* pred e'
=>*pred nil        = nil
=>*pred (cons x p) = cons (=>pred x) (=>*pred p)

=>*isZ : {e e' : Exp} -> e =>* e' -> isZ e =>* isZ e'
=>*isZ nil        = nil
=>*isZ (cons x p) = cons (=>isZ x) (=>*isZ p)

=>*if : {e e' e0 e1 : Exp} -> e =>* e' -> if e e0 e1 =>* if e' e0 e1
=>*if nil        = nil
=>*if (cons x p) = cons (=>if x) (=>*if p)


------------------------------------------------------------------------
-- 4.  The two semantics agree: if e ⇓ v then e =>* v
--
-- by induction on the derivation of e ⇓ v ; each big step is replayed
-- as: reduce the subexpression, then take the computation step
------------------------------------------------------------------------

sound⇓ : {e v : Exp} -> e ⇓ v -> e =>* v

sound⇓ vtrue    = nil
sound⇓ vfalse   = nil
sound⇓ v0       = nil

sound⇓ (⇓suc p) = =>*suc (sound⇓ p)

sound⇓ (⇓isZ0 p) = isTrans (=>*isZ (sound⇓ p)) (oneStep =>isZ0)
sound⇓ (⇓isZS p) = isTrans (=>*isZ (sound⇓ p)) (oneStep =>isZS)

sound⇓ (⇓pred0 p) = isTrans (=>*pred (sound⇓ p)) (oneStep =>pred0)
sound⇓ (⇓predS p) = isTrans (=>*pred (sound⇓ p)) (oneStep =>predS)

sound⇓ (⇓iftrue p q)  = isTrans (=>*if (sound⇓ p)) (cons =>true (sound⇓ q))
sound⇓ (⇓iffalse p q) = isTrans (=>*if (sound⇓ p)) (cons =>false (sound⇓ q))


------------------------------------------------------------------------
-- 5.  Typing the big step semantics
--
-- The analogue of preservation: evaluation does not change the type.
------------------------------------------------------------------------

⇓preservation : {e v : Exp} -> {T : Typ} -> e :: T -> e ⇓ v -> v :: T

⇓preservation eT vtrue  = eT
⇓preservation eT vfalse = eT
⇓preservation eT v0     = eT

⇓preservation (typeS eT) (⇓suc p) = typeS (⇓preservation eT p)

⇓preservation (typeZ eT) (⇓isZ0 p) = typet
⇓preservation (typeZ eT) (⇓isZS p) = typef

⇓preservation (typep eT) (⇓pred0 p) = type0
⇓preservation (typep eT) (⇓predS p) = predlem (⇓preservation eT p)
 where
  predlem : {v : Exp} -> suc v :: nat -> v :: nat
  predlem (typeS vT) = vT

⇓preservation (typeif eT eT0 eT1) (⇓iftrue p q)  = ⇓preservation eT0 q
⇓preservation (typeif eT eT0 eT1) (⇓iffalse p q) = ⇓preservation eT1 q


------------------------------------------------------------------------
-- Exercises
--
-- 1. Show that => is deterministic: if e => e1 and e => e2 then e1 ≡ e2
-- 2. Show the converse of sound⇓ : if e =>* v and isVal v then e ⇓ v
--    (first prove:  e => e'  and  e' ⇓ v  imply  e ⇓ v)
-- 3. Show that isZ true has no value: ¬ (Σ Exp (λ v -> isZ true ⇓ v))
-- 4. Show that a well typed e has a value: e :: T implies Σ Exp (λ v -> e ⇓ v)
--    Which induction does this need?
------------------------------------------------------------------------
