module bb2 where

-- Turing machines in Agda
--
-- 1. Turing machines as programs: the Busy Beaver champions for 2, 3, 4 states
-- 2. Non-termination as a proposition, and a proof that a machine never stops
--
-- Everything is defined from scratch: no library is needed.

------------------------------------------------------------------------
-- Basic data types
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

infixr 5 _::_

-- Dependent pairs (Σ-types); product and sum as special cases

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ

infixr 4 _,_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 4 _×_

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- A few numbers, to bound the runs below

five : Nat
five = suc (suc (suc (suc (suc zero))))

ten : Nat
ten = suc (suc (suc (suc (suc five))))

twice : Nat → Nat
twice zero    = zero
twice (suc n) = suc (suc (twice n))

twenty : Nat
twenty = twice ten

big : Nat                       -- 320
big = twice (twice (twice (twice twenty)))

------------------------------------------------------------------------
-- Turing machines
------------------------------------------------------------------------

-- Symbols: zero = blank, one = mark
data Symbol : Set where
  zero one : Symbol

-- States, with a distinguished halting state
data State : Set where
  qA qB qC qD qHalt : State

-- Head movements
data Dir : Set where
  L R : Dir

-- The tape: the cells to the left of the head (nearest first), the cell
-- under the head, the cells to the right.  Only finitely many cells are
-- stored; the rest are blank.
record Tape : Set where
  constructor tape
  field
    left  : List Symbol
    head  : Symbol
    right : List Symbol

open Tape

move : Dir → Tape → Tape
move L (tape []        h r) = tape [] zero (h :: r)
move L (tape (l :: ls) h r) = tape ls l (h :: r)
move R (tape l h [])        = tape (h :: l) zero []
move R (tape l h (r :: rs)) = tape (h :: l) r rs

-- A machine is its transition function: from the current state and the
-- symbol under the head, give the new state, the symbol to write, and
-- where to move.
Transition : Set
Transition = State → Symbol → State × Symbol × Dir

-- One step of execution
step : Transition → State → Tape → State × Tape
step δ s t = go (δ s (head t))
  where
    go : State × Symbol × Dir → State × Tape
    go (s' , sym , d) = (s' , move d (tape (left t) sym (right t)))

-- Run for at most n steps, stopping early in the halting state.
-- This always terminates: n decreases at each call.
run : Nat → Transition → State → Tape → State × Tape
run zero    δ s t = (s , t)
run (suc n) δ s t = go (step δ s t)
  where
    go : State × Tape → State × Tape
    go (qHalt , t') = (qHalt , t')
    go (s'    , t') = run n δ s' t'

-- Start in qA on a blank tape
initialTape : Tape
initialTape = tape [] zero []

srun : Nat → Transition → State × Tape
srun n δ = run n δ qA initialTape

------------------------------------------------------------------------
-- The Busy Beaver champions
------------------------------------------------------------------------

-- BB(2) = 6 steps
bb2 : Transition
bb2 qA zero = (qB    , one , R)
bb2 qA one  = (qB    , one , L)
bb2 qB zero = (qA    , one , L)
bb2 qB one  = (qHalt , one , R)
bb2 q  s    = (qHalt , s   , R)      -- unused states

-- BB(3) = 21 steps
bb3 : Transition
bb3 qA zero = (qB    , one , R)
bb3 qA one  = (qC    , one , L)
bb3 qB zero = (qA    , one , L)
bb3 qB one  = (qB    , one , R)
bb3 qC zero = (qB    , one , L)
bb3 qC one  = (qHalt , one , R)
bb3 q  s    = (qHalt , s   , R)

-- BB(4) = 107 steps, leaves 13 marks on the tape (Brady 1983)
bb4 : Transition
bb4 qA zero = (qB    , one  , R)
bb4 qA one  = (qB    , one  , L)
bb4 qB zero = (qA    , one  , L)
bb4 qB one  = (qC    , zero , L)
bb4 qC zero = (qHalt , one  , R)
bb4 qC one  = (qD    , one  , L)
bb4 qD zero = (qD    , one  , R)
bb4 qD one  = (qA    , zero , R)
bb4 q  s    = (qHalt , s    , R)

-- Evaluate these with C-c C-n
runBB2 : State × Tape
runBB2 = srun big bb2

runBB3 : State × Tape
runBB3 = srun big bb3

runBB4 : State × Tape
runBB4 = srun big bb4

-- Exercise: write a function counting the number of steps until the machine
-- halts, and check that bb4 halts after 107 steps.

------------------------------------------------------------------------
-- Machines that never stop
------------------------------------------------------------------------

-- The simplest one: stay in qA and move right forever
forever : Transition
forever qA zero = (qA , zero , R)
forever q  s    = (q  , s    , R)

-- A slightly less trivial one: alternate between qA and qB
alternate : Transition
alternate qA s = (qB , one  , R)
alternate qB s = (qA , zero , R)
alternate q  s = (qHalt , s , R)

-- Running them just gives back a state and a tape; no amount of running
-- can show that a machine never stops.  For that we need a proof.
runForever : State × Tape
runForever = srun big forever

------------------------------------------------------------------------
-- Propositions as types
------------------------------------------------------------------------

-- The false proposition: no proof
data ⊥ : Set where

-- The true proposition: one proof
data ⊤ : Set where
  tt : ⊤

-- Negation: a proof of ¬ A is a function from proofs of A to proofs of ⊥
¬ : Set → Set
¬ A = A → ⊥

-- "The state s is the halting state", as a proposition depending on s
Stop : State → Set
Stop qHalt = ⊤
Stop _     = ⊥

-- "The state s is qA"
QA : State → Set
QA qA = ⊤
QA _  = ⊥

-- A state cannot be both qA and halting.  Proof by cases on the state;
-- in each case the proof is trivial once the types have computed.
QA-notStop : (s : State) → QA s → ¬ (Stop s)
QA-notStop qA    p h = h
QA-notStop qB    p h = p
QA-notStop qC    p h = p
QA-notStop qD    p h = p
QA-notStop qHalt p h = p

-- "The machine δ never stops": for every n, after n steps we are not halted
neverStop : Transition → Set
neverStop δ = (n : Nat) → ¬ (Stop (fst (srun n δ)))

-- "The machine δ stops": for some n, after n steps we are halted
willStop : Transition → Set
willStop δ = Σ Nat (λ n → Stop (fst (srun n δ)))

-- The machine `forever` stays in qA, whatever the tape to the left.
-- Proof by induction on n.  Note that the statement has to be generalised
-- to an arbitrary tape on the left, since each step adds one cell there.
staysInQA : (n : Nat) (l : List Symbol) → QA (fst (run n forever qA (tape l zero [])))
staysInQA zero    l = tt
staysInQA (suc n) l = staysInQA n (zero :: l)

theorem : neverStop forever
theorem n = QA-notStop (fst (srun n forever)) (staysInQA n [])

-- Exercise: prove  neverStop alternate.
-- Hint: define QB, and prove by induction that after n steps the machine is
-- in qA or in qB.

------------------------------------------------------------------------
-- What we cannot expect to prove
------------------------------------------------------------------------

-- For a given machine, deciding which of the two holds is the halting
-- problem.  So we do not expect to prove the following for all δ.
Halting : Transition → Set
Halting δ = neverStop δ + willStop δ

------------------------------------------------------------------------
-- Equality, and proofs by computation
------------------------------------------------------------------------

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

-- These are checked by the type checker itself: it runs the machine.
bb2-halts : fst runBB2 ≡ qHalt
bb2-halts = refl

bb4-halts : fst runBB4 ≡ qHalt
bb4-halts = refl

forever-runs : fst runForever ≡ qA
forever-runs = refl
