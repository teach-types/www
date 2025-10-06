-- Parse monad

module Parser.Monad (Token ParseError : Set) (leftoverTokens : ParseError) where

open import Prelude

private
  variable
    A B : Type

Input = List Token

-- Result A = ParseError ⊎ (A × Input)

data Result (A : Type) : Type where
  parsed : (x : A) (rest : Input) → Result A
  failed : (err : ParseError) → Result A

-- Parser A = Input → ParseError ⊎ (A × Input)

Parser : Set → Set
Parser A = Input → Result A

_>>=ʳ_ : Result A → (A → Parser B) → Result B
parsed x rest >>=ʳ k = k x rest
failed err    >>=ʳ k = failed err

-- Parser is a monad.

_>>=_ : Parser A → (A → Parser B) → Parser B
(p >>= k) inp = p inp >>=ʳ k

pure : A → Parser A
pure = parsed

-- Functoriality.

_<$>_ : (A → B) → Parser A → Parser B
f <$> p = do
  a ← p
  pure (f a)

_<&>_ : Parser A → (A → B) → Parser B
_<&>_ = flip _<$>_

-- Combining with parsers that have no output.

_<$_ : A → Parser ⊤ → Parser A
a <$ p = do
  _ ← p
  pure a

_<*ʳ_ : Result A → Parser ⊤ → Result A
r <*ʳ q = r >>=ʳ λ a → a <$ q

_<*_ : Parser A → Parser ⊤ → Parser A
p <* q = do
  a ← p
  a <$ q

-- Token parser

pToken : (Maybe Token → List Token → Result A) → Parser A
pToken f []       = f nothing []
pToken f (t ∷ ts) = f (just t) ts

-- Parse entire input

parse : Parser A → List Token → Result A
parse p ts = case p ts of λ where
  (parsed x []) → parsed x []
  (parsed x ts) → failed leftoverTokens
  (failed err) → failed err
