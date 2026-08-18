-- Encoding natural numbers with addition and multiplication as typed lambda terms

module ChurchNumerals where

open import Prelude
open import Prelude.Pretty
open import Term
open import NatSignature
open import Check  using (Scope; empty; cons; check; infer; inferred)
open import Lexer  using (lex)
open import Parser using (parseExp; parsed; failed)
import Eval

private
  variable
    a b : Ty
    Γ Δ : Context

-- Parse, type-check and evaluate an lambda-term over the {zero,suc} signature.
-- Errors are

error : ℕ
error = 5317  -- "LIES" in calculator encoding

run : String → String
run s = case parseExp (lex s) of λ where
  (parsed e []) → case infer scopeℕ e of λ where
    (inferred tℕ t) → ℕ.show (evalℕ t)
    _ → "TYPE ERROR"
  (failed err) → "PARSE ERROR"
  _ → "IMPOSSIBLE"

-- Church numeral n is n-fold application of a given function to a given value.

num : ℕ → String
num n = "λ (f : ℕ → ℕ) → λ (x : ℕ) → " <> ℕ.fold "x" (λ x → "f" <+> parens x) n

-- Adding Church numerals.

add : String
add = "λ (n : (ℕ → ℕ) → ℕ → ℕ) → λ (m : (ℕ → ℕ) → ℕ → ℕ) → λ (f : ℕ → ℕ) → λ (x : ℕ) → n f (m f x)"

-- Multiplying Church numerals.

mul : String
mul = "λ (n : (ℕ → ℕ) → ℕ → ℕ) → λ (m : (ℕ → ℕ) → ℕ → ℕ) → λ (f : ℕ → ℕ) → λ (x : ℕ) → n (m f) x"

-- Examples.

s4+2 : String
s4+2 = parens add <+> parens (num 4) <+> parens (num 2) <+> "suc" <+> "zero"

4+2 : String
4+2 = run s4+2

s5*3 : String
s5*3 = parens mul <+> parens (num 5) <+> parens (num 3) <+> "suc" <+> "zero"

5*3 : String
5*3 = run s5*3
