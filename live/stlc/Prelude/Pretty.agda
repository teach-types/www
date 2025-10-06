-- Mini pretty printing library

module Prelude.Pretty where

open import Prelude
open String public using () renaming (_++_ to infixr 6 _<>_)

infixr 6 _<+>_

_<+>_ : String → String → String
s <+> t = s <> " " <> t

parens : String → String
parens s = "(" <> s <> ")"
