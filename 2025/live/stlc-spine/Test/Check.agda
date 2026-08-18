-- Testing the type checker

module Test.Check where

open import Prelude
open import Exp
open import Term
open import Check

private
  variable
    a b : Ty
    Γ : Context

open import Lexer
open import Parser

`a : Ty
`a = ` "a"

`b : Ty
`b = ` "b"

K-term : Check [] (`a ⇒ (`b ⇒ `a))
K-term = check empty (lam (uBind "x") (lam (uBind "y") (Exp.var "x"))) _
  -- checked (abs (abs (Term.var (suc zero))))

open import NatSignature

zero-term : Infer Γℕ
zero-term = infer scopeℕ zero-exp

-- Error is "zero"

error-term : Term Γℕ tℕ
error-term = Term.var (suc zero)

infer! : Exp → ∃ λ a → Term Γℕ a
infer! e = case infer scopeℕ e of λ where
  (inferred a t) → a , t
  _ → _ , error-term

add-term : _
add-term = infer! add-exp

open import ChurchNumerals

inf = infer! ∘ parse! ∘ lex

num-term : ℕ → _
num-term = inf ∘ num

4+2-term : _
4+2-term = inf s4+2

-- -}
-- -}
