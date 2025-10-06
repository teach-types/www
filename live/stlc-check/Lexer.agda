-- Turn a character string into a token string.
--
-- Implemented as output automaton.

module Lexer where

open import Prelude

data Symbol : Type where
  lpar   : Symbol  -- '('
  rpar   : Symbol  -- ')'
  colon  : Symbol  -- ':'
  arrow  : Symbol  -- '→'
  lambda : Symbol  -- 'λ'

-- Decidable equality for Symbol

_≟_ : (x y : Symbol) → Dec (x ≡ y)
-- Same symbols are equal
lpar   ≟ lpar   = yes refl
rpar   ≟ rpar   = yes refl
colon  ≟ colon  = yes refl
arrow  ≟ arrow  = yes refl
lambda ≟ lambda = yes refl
-- Others are inequal
lpar   ≟ rpar   = no λ ()
lpar   ≟ colon  = no λ ()
lpar   ≟ arrow  = no λ ()
lpar   ≟ lambda = no λ ()
rpar   ≟ lpar   = no λ ()
rpar   ≟ colon  = no λ ()
rpar   ≟ arrow  = no λ ()
rpar   ≟ lambda = no λ ()
colon  ≟ lpar   = no λ ()
colon  ≟ rpar   = no λ ()
colon  ≟ arrow  = no λ ()
colon  ≟ lambda = no λ ()
arrow  ≟ lpar   = no λ ()
arrow  ≟ rpar   = no λ ()
arrow  ≟ colon  = no λ ()
arrow  ≟ lambda = no λ ()
lambda ≟ lpar   = no λ ()
lambda ≟ rpar   = no λ ()
lambda ≟ colon  = no λ ()
lambda ≟ arrow  = no λ ()

data Token : Type where
  symbol : (t : Symbol) → Token
  ident  : (x : String) → Token  -- non-empty string of non-space non-symbol characters

private

  -- We have just "one" state, but it can store an identifier prefix of arbitrary length.
  -- Formally, this is not a finite automaton.

  data State : Type where
    state : (rev-chars : List Char) → State  -- characters that will form an ident

  pattern initial-state = state []

  -- The result of a step is a new step and a (possibly empty) list of tokens
  -- output by the automaton during the step.

  -- Push a new character onto the stack of saved characters.

  save-char : (c : Char) (s : State) → State
  save-char c (state rev-chars) = state (c ∷ rev-chars)

  record Step : Type where
    constructor stepped; no-eta-equality; pattern
    field
      new-state : State
      output    : List Token
  open Step

  -- Output the stored characters (if any) as identifier token.

  cons-ident : (rev-chars : List Char) → List Token → List Token
  cons-ident [] = id
  cons-ident rev-chars = ident (String.fromList (reverse rev-chars)) ∷_
    -- here we lose the information that cs is non-empty

  -- Output the given tokens, possibly prefixed by an identifier token
  -- harvested from the state.

  step-symbol : (s : State) (t : List Token) → Step
  step-symbol (state rev-chars) ts = stepped initial-state (cons-ident rev-chars ts)

  -- Transition function of the automaton.

  step : (s : State) (c : Char) → Step
  step s '(' = step-symbol s (symbol lpar   ∷ [])
  step s ')' = step-symbol s (symbol rpar   ∷ [])
  step s ':' = step-symbol s (symbol colon  ∷ [])
  step s '→' = step-symbol s (symbol arrow  ∷ [])
  step s 'λ' = step-symbol s (symbol lambda ∷ [])
  step s c = if isSpace c then step-symbol s [] else stepped (save-char c s) []

  -- Iterating the transition function.

  run : (s : State) (cs : List Char) → List Token
  run s (c ∷ cs) = case step s c of λ where
    (stepped s' ts) → ts ++ run s' cs
  run (state rev-chars) [] = cons-ident rev-chars []

-- Entrypoint: fully lex the given string.

lex : (s : String) → List Token
lex s = run initial-state (String.toList s)

-- Test

app-string : String
app-string = "x x"

app-tokens : List Token
app-tokens = lex app-string

id-string : String
id-string = "λx→x"

id-tokens : List Token
id-tokens = lex id-string

id-typed-string : String
id-typed-string = "λ (x : (ℕ → ℕ) → ℕ → ℕ) → x"

id-typed-tokens : List Token
id-typed-tokens = lex id-typed-string

one-string : String
one-string = "λ x → λ y → x y"

one-tokens : List Token
one-tokens = lex one-string

one-par-string : String
one-par-string = "λ x → λ y → x(y)"

one-par-tokens : List Token
one-par-tokens = lex one-par-string

K-string : String
K-string = "λ x → λ y → x"

K-tokens : List Token
K-tokens = lex K-string

S-string : String
S-string = "λ x → λ y → λ z → x z (y z)"

S-tokens : List Token
S-tokens = lex S-string

sapp-string : String
sapp-string = "λ x → x x"

sapp-tokens : List Token
sapp-tokens = lex sapp-string

zero-string : String
zero-string = "λ (f : ℕ → ℕ) → λ (x : ℕ) → x"

zero-tokens : List Token
zero-tokens = lex zero-string

add-string : String
add-string = "λ (n : (ℕ → ℕ) → ℕ → ℕ) → λ (m : (ℕ → ℕ) → ℕ → ℕ) → λ (f : ℕ → ℕ) → λ (x : ℕ) → n f (m f x)"

add-tokens : List Token
add-tokens = lex add-string
