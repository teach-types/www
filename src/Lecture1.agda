
module Lecture1 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

-- Some useful Agda commands (see the user manual for more)
--   C-c C-l      type check the buffer
--   C-c C-n      evaluate an expression (can use local variable if called from a hole)
--   C-c C-c      perform case analysis (type variable into hole)
--   C-c C-,      goal type and context
--   C-c C-Space  fill a hole with a term
--   C-c C-r      fill a hole with a function applied to an appropriate number of fresh holes
--   \to or \->   unicode arrow: →

-- Agda functions are commonly defined by pattern matching.

not : Bool → Bool
not false = true
not true  = false

-- Infix operators can be declared by using underscores the name. Types and constructors
-- can also be operators.
_&&_ : Bool → Bool → Bool
false && y = false
true  && y = y

infixr 3 _&&_  -- operators can be given precedences like in Haskell

-- Declaring a 'variable' tells Agda that you want to use it as a type variable. Similar to
-- how in Haskell
--   id :: a -> a
-- really means
--   id :: forall a. a -> a
-- In Haskell any lower case identifier is a type variable, but in Agda you have to declare them
-- before using them.
variable
  A : Set

-- Operators are not limited to infix operators, underscore can go whereever you want. There are
-- also no restrictions on what identifier characters can be used in name, any non-whitespace unicode
-- characters are fine (with some restrictions for reserved characters).
-- This means that spaces are important in Agda: 1+2 is a valid identifier, and 1 + 2 computes to 3.

if_then_else_ : Bool → A → A → A  -- if is polymorphic in the return type
if false then x else y = y
if true  then x else y = x

-- Exercise: Implement some more functions on booleans,
--            for instance, or (_||_) and equivalence/equality (_<=>_)

-- Exercise: Implement the factorial function by pattern on the natural number argument.

-- A simple expression language

module SimpleTypes where

  -- Agda is declare before use (in contrast to Haskell). Mutual recursion can be expression
  -- using a `mutual` block.
  mutual
    data Expr : Set where
      lit : Nat → Expr
      add : Expr → Expr → Expr
      if  : Cond → Expr → Expr → Expr

    data Cond : Set where
      lt  : Expr → Expr → Cond
      and : Cond → Cond → Cond
      neg : Cond → Cond

  -- You can also express mutual recursion by declaring things before you use them.
  eval : Expr → Nat
  cond : Cond → Bool

  eval (lit n)    = n
  eval (add a b)  = eval a + eval b
  eval (if c a b) = if cond c then eval a else eval b

  cond (lt a b)  = eval a < eval b
  cond (and a b) = cond a && cond b
  cond (neg a)   = not (cond a)

  ex : Expr
  ex = add (lit 4) (add (lit 1) (lit 2))

-- Indexed types.
-- Having separate data types for expressions and conditional is very
-- rigid and doesn't scale well. For instance, if we wanted if
-- expressions to be usable in conditionals we'd have to duplicat the if
-- constructor and the handling of it in the eval functions. A better
-- way is to have a single *indexed* data type, where the index tells us
-- if the expression is a natural number expression or a conditional.

-- First we define a data type for our object-level types (numbers and
-- booleans).
data Ty : Set where
  nat  : Ty
  bool : Ty

variable t : Ty

-- Then we define an expression data type indexed by an object-level type.
-- Now each constructor can target a different object-level type, and the if
-- constructor can be polymorphic in the type.
data Expr : Ty → Set where
  lt  : Expr nat → Expr nat → Expr bool
  and : Expr bool → Expr bool → Expr bool
  neg : Expr bool → Expr bool
  lit : Nat → Expr nat
  add : Expr nat → Expr nat → Expr nat
  if  : Expr bool → Expr t → Expr t → Expr t

-- Mapping object-level types to Agda types.
Value : Ty → Set
Value nat  = Nat
Value bool = Bool

-- eval now takes an expression of object type t and computes a value
-- of the corresponding Agda type.
eval : Expr t → Value t
eval (lt e e₁)    = eval e < eval e₁
eval (and e e₁)   = eval e && eval e₁
eval (neg e)      = not (eval e)
eval (lit n)      = n
eval (add e e₁)   = eval e + eval e₁
eval (if e e₁ e₂) = if eval e then eval e₁ else eval e₂

ex : Expr nat
ex = if (lt (lit 0) (lit 1)) (add (lit 1) (lit 2)) (lit 0)

-- Exercise: Add multiplication to the language

-- Exercise: Define `eq : Expr nat → Expr nat → Expr bool and `or : Expr bool → Expr bool → Expr bool`
--           using the existing language structures (i.e. without changing the datatypes)

-- Exercise: Write down some example expressions and evaluate them with `eval` using
--           C-c C-n.
