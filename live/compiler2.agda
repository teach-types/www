module compiler2 where

------------------------------------------------------------------------
-- Correctness of a compiler for arithmetic expressions
--
-- The example is the one of
--   J. McCarthy and J. Painter, Correctness of a compiler for
--   arithmetic expressions, 1967
-- and the question itself goes back to
--   A. Turing, Checking a large routine, 1949
--
-- The first -machine checked- proof of compiler correctness is
--   R. Milner and R. Weyhrauch, Proving compiler correctness in a
--   mechanized logic, 1972   (Stanford LCF)
-- and the same statement, at scale, is
--   X. Leroy, Formal certification of a compiler back-end, 2006
--   (CompCert), and CakeML (Myreen et al., HOL)
--
-- Two semantics are given: a -denotational- one for the source
-- (the function eval) and an -operational- one for the target
-- (the relation => on machine states).  Correctness relates them.
--
-- This is compiler.agda with the chain notation _using<_>_ removed:
-- the proof of correct-aux is written directly with trans and oneStep.
-- Nothing is lost except readability; the two proofs are the same term.
------------------------------------------------------------------------

open import Agda.Primitive renaming (Set to Type)


------------------------------------------------------------------------
-- 1.  Naturals
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

one : Nat
one = suc zero

two : Nat
two = suc one


------------------------------------------------------------------------
-- 2.  Environments: Fin n is the type of the n variables
------------------------------------------------------------------------

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

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

record ⊤ : Set where
 constructor tt

-- Vec A n is defined by -recursion- on n, not as an inductive family

Vec : Set -> Nat → Set
Vec A zero    = ⊤
Vec A (suc n) = A × Vec A n

lookup : {A : Set}{n : Nat} → Fin n → Vec A n → A
lookup zero    (x , xs) = x
lookup (suc i) (x , xs) = lookup i xs


------------------------------------------------------------------------
-- 3.  The source language, and its denotational semantics
--
-- An expression with n free variables is an element of Exp n;
-- its meaning is a function from environments Vec Nat n to Nat.
------------------------------------------------------------------------

data Exp (n : Nat) : Set where
  lit : Nat → Exp n
  var : Fin n → Exp n
  add : Exp n → Exp n → Exp n

eval : {n : Nat} → Exp n → Vec Nat n → Nat
eval (lit k)   ρ = k
eval (var i)   ρ = lookup i ρ
eval (add e f) ρ = eval e ρ + eval f ρ

-- the expression (x + 1) + x, with x the only variable

exmp : Exp (suc zero)
exmp = add (add (var zero) (lit one)) (var zero)

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

-- in the environment x = 2 it denotes 5

testeval : eval exmp (two , tt) ≡ suc (suc (suc two))
testeval = refl


------------------------------------------------------------------------
-- 4.  The target: a stack machine
--
-- A code is a list of instructions, written here as a -tree- whose
-- spine is the rest of the code; HALT ends it.
------------------------------------------------------------------------

data Code (n : Nat) : Set where
  PUSH : Nat   -> Code n → Code n
  LOAD : Fin n -> Code n → Code n
  ADD  :          Code n -> Code n
  HALT :          Code n

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

infixr 5 _::_

Stack = List Nat

-- a state of the machine: the code left to run, the environment,
-- and the stack

record State : Set where
 constructor state
 field
  n     : Nat
  instr : Code n
  env   : Vec Nat n
  stack : Stack

open State

-- the operational semantics of the machine: one rule per instruction.
-- Note that ADD pops x then y and pushes y + x : the operand pushed
-- -first- is the one deeper in the stack

data _=>_ : State -> State -> Set where

 =>PUSH : {n k : Nat} {p : Code n} {r : Vec Nat n} {s : Stack} ->
   ----------------------------------------------------------------
   state n (PUSH k p) r s => state n p r (k :: s)

 =>LOAD : {n : Nat}{i : Fin n}{p : Code n} {r : Vec Nat n} {s : Stack} ->
   ----------------------------------------------------------------------
   state n (LOAD i p) r s => state n p r (lookup i r :: s)

 =>ADD : {n : Nat}{p : Code n} {r : Vec Nat n} {s : Stack} {x y : Nat} ->
   ----------------------------------------------------------------------
   state n (ADD p) r (x :: y :: s) => state n p r ((y + x) :: s)

-- there is no rule for HALT: a state with code HALT is a final state


------------------------------------------------------------------------
-- 5.  The compiler
--
-- Written with an accumulator: compile-aux e acc is the code which
-- evaluates e, pushes its value, and then continues with acc.
-- This is what avoids having to reason about concatenation of code.
------------------------------------------------------------------------

compile-aux : {n : Nat} → Exp n → Code n → Code n
compile-aux (lit k)   acc = PUSH k acc
compile-aux (var i)   acc = LOAD i acc
compile-aux (add e f) acc = compile-aux e (compile-aux f (ADD acc))

compile : {n : Nat} → Exp n → Code n
compile e = compile-aux e HALT

testcompile :
  compile exmp ≡ LOAD zero (PUSH one (ADD (LOAD zero (ADD HALT))))
testcompile = refl


------------------------------------------------------------------------
-- 6.  Running the machine: the reflexive transitive closure of =>
------------------------------------------------------------------------

data _=>*_ : State -> State -> Set where
 nil  : {s : State} -> s =>* s
 cons : {s1 s2 s3 : State} -> s1 => s2 -> s2 =>* s3 -> s1 =>* s3

trans : {s1 s2 s3 : State} -> s1 =>* s2 -> s2 =>* s3 -> s1 =>* s3
trans nil        q = q
trans (cons x p) q = cons x (trans p q)

oneStep : {x y : State} -> x => y -> x =>* y
oneStep p = cons p nil


------------------------------------------------------------------------
-- 7.  Correctness
--
-- The statement one would like is about compile e ; but it is not
-- provable by induction as it stands.  One has to -generalise- it,
-- over the accumulator acc and over the stack s.  This is the whole
-- point of the proof: finding the statement the induction can carry.
--
-- The proof itself is then a structural induction on the expression.
------------------------------------------------------------------------

correct-aux : {n : Nat} (e : Exp n)(r : Vec Nat n)(s : Stack)(acc : Code n)
         → state n (compile-aux e acc) r s =>* state n acc r (eval e r :: s)

correct-aux {n} (lit k) r s acc = oneStep =>PUSH
correct-aux {n} (var i) r s acc = oneStep =>LOAD

correct-aux {n} (add e0 e1) r s acc =
  trans (correct-aux e0 r s (compile-aux e1 (ADD acc)))
        (trans (correct-aux e1 r (eval e0 r :: s) (ADD acc))
               (oneStep =>ADD))

-- The three pieces, in order:
--   run the code of e0, leaving eval e0 r on top of s
--   run the code of e1, leaving eval e1 r on top of that
--   one ADD step, which pops both and pushes eval e0 r + eval e1 r
-- The first and the last state of the chain need no justification at
-- all: compile-aux (add e0 e1) acc and eval (add e0 e1) r are already
-- -definitionally- what we need, so Agda accepts the term as it stands.

-- the theorem itself is the special case acc = HALT

correct-compile : {n : Nat} (e : Exp n)(r : Vec Nat n)(s : Stack)
         → state n (compile e) r s =>* state n HALT r (eval e r :: s)
correct-compile e r s = correct-aux e r s HALT


------------------------------------------------------------------------
-- Exercises
--
-- 1. Why is the statement
--      state n (compile e) r [] =>* state n HALT r (eval e r :: [])
--    not provable directly by induction on e?
-- 2. Add a constructor  mul : Exp n -> Exp n -> Exp n  and an
--    instruction MUL, and extend the proof.  How much has to change?
-- 3. Give a -small step- semantics for the source language, with states
--    Exp n × Vec Nat n, by the rules
--      e0 => e0' implies add e0 e1 => add e0' e1 , etc.
--    and relate it to eval.
-- 4. Define the machine as a -function- run : Nat -> State -> State
--    and compare proving correctness of that with the relational proof.
------------------------------------------------------------------------
