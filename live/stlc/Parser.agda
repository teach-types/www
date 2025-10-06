--  Parse a token stream into a lambda-calculus expression.

module Parser where

open import Prelude
open import Exp
open import Lexer
import Parser.Monad

private
  variable
    A B : Type

--  LBNF Grammar (LR):
--  ------------------
--
--  Types.
--
--    _.       Ty1  ::= '(' Type ')'
--    TId.     Ty1  ::= Ident
--    _        Ty   ::= Ty1
--    TArr.    Ty   ::= Ty1 '→' Ty
--
-- Binders.
--
--    UBind.   Bind ::= Ident
--    TBind.   Bind ::= '(' Ident ':' Type ')'
--
-- Expressions.
--
--    _.       Exp2 ::= '(' Exp ')'
--    EId.     Exp2 ::= Ident
--    _.       Exp1 ::= Exp2
--    EApp.    Exp1 ::= Exp2 Exp1
--    _.       Exp  ::= Exp1
--    ELam.    Exp  ::= 'λ' Bind '→' Exp
--    EAppLam. Exp  ::= Exp1 'λ' Bind '→' Exp
--
--  We convert this grammar into LL so we can implement a simple recursive-descent parser.
--
--  Types.
--
--    TPar.  Ty    ::= '(' Ty ')' Tys
--    TId.   Ty    ::= Id         Tys
--
--    TFun.  Tys   ::= '→' Ty Tys
--    TEmp.  Tys   ::= {- empty -}
--
--  Expressions.
--
--    APar.  Atm  ::= '(' Exp ')'
--    AId.   Atm  ::= Ident
--
--    Exp.   Exp  ::= Exps              -- Post-process the list
--
--    Exps.  Exps ::= Atm Rest          -- Ident, '('
--    ELam.  Exps ::= 'λ' Bind '→' Exp
--
--    REmp.  Rest ::= {- empty -}
--    RAtm.  Rest ::= Exp               -- Ident, '(', 'λ'


-- Parser infrastructure

Input = List Token

data ParseError : Type where
  symbolExpected     : Symbol → ParseError
  identExpected      : ParseError
  typeExpected       : ParseError
  expressionExpected : ParseError
  binderExpected     : ParseError
  leftoverTokens     : ParseError
  -- withTokens         : ParseError → Input → ParseError

module P = Parser.Monad Token ParseError leftoverTokens
open P using (Parser; Result; pure; _>>=_; _<$>_; _<&>_; pToken; parse)
open P public using (parsed; failed)

-- Token parsers

pSymbol : Symbol → Parser ⊤
pSymbol s = pToken λ where
    (just (symbol s')) rest →
      case s ≟ s' of λ where
        (yes _) → parsed _ rest
        (no  _) → fail
    _ _ → fail
  where
    fail = failed (symbolExpected s)

pIdent : Parser Ident
pIdent = pToken λ where
  (just (ident x)) rest → parsed x rest
  _ _ → failed identExpected

-- Grammar

--    AId.   Atm  ::= Ident
--    APar.  Atm  ::= '(' Exp ')'
--
--    Exp.   Exp  ::= Exps
--
--    ELam.  Exps ::= 'λ' Bind '→' Exp
--    Exps.  Exps ::= Atm Rest          -- Ident, '('
--
--    REmp.  Rest ::= {- empty -}
--    RAtm.  Rest ::= Exp               -- Ident, '(', 'λ'

-- Converting a snoc-list of expression into a nested application

toExp : List⁺ Exp → Exp
toExp = List⁺.foldr₁ (flip app)

-- Agda does not recognize the parser as terminating,
-- and the argument is not trivial, so we take a short cut.

{-# TERMINATING #-}
mutual
  -- Atomic expressions

  pAtm : Parser Exp
  pAtm (ident x     ∷ ts) = ts |> pure (var x)
  pAtm (symbol lpar ∷ ts) = ts |> do
    e ← pExp
    _ ← pSymbol rpar
    pure e
  pAtm _ = failed expressionExpected

  -- Expressions

  pExp : Parser Exp
  pExp = pExps []

  -- Expression following a snoc-list of expressions

  pExps : List Exp → Parser Exp
  pExps es⃖ (symbol lambda ∷ ts) = ts |> do
    b ← pBind
    _ ← pSymbol arrow
    e ← pExp
    pure (toExp (abs b e ∷ es⃖))
      -- Note: No more applications can follow a λ.
  pExps es⃖ = do
    e  ← pAtm
    pRest (e ∷ es⃖)

  -- Maybe expression following a non-empty snoc-list of expressions

  pRest : List⁺ Exp → Parser Exp
  -- Case: More coming...
  pRest es⃖ ts@(ident x       ∷ _) = ts |> pExps (List⁺.toList es⃖)
  pRest es⃖ ts@(symbol lpar   ∷ _) = ts |> pExps (List⁺.toList es⃖)
  pRest es⃖ ts@(symbol lambda ∷ _) = ts |> pExps (List⁺.toList es⃖)
  -- Case: No more expressions coming.
  pRest es⃖ ts = ts |> pure (toExp es⃖)

  -- Binder

  pBind : Parser Bind
  pBind (ident x ∷ ts) = ts |> pure (uBind x)
  pBind (symbol lpar ∷ ts) = ts |> do
    x ← pIdent
    _ ← pSymbol colon
    a ← pTy
    _ ← pSymbol rpar
    pure (tBind x a)
  pBind _ = failed binderExpected

  -- Type expressions

  pTy : Parser Ty
  pTy (symbol lpar ∷ ts) = ts |> do
    a  ← pTy
    _  ← pSymbol rpar
    as ← pTys
    pure (mkTy a as)
  pTy (ident x ∷ ts) = ts |> do
    as ← pTys
    pure (mkTy (` x) as)
  pTy _ = failed typeExpected

  pTys : Parser (List Ty)
  pTys (symbol arrow ∷ ts) = ts |> do
    a ← pTy
    as ← pTys
    pure (a ∷ as)
  pTys ts = ts |> pure []

-- Entry point for expressions

parseExp : Input → Result Exp
parseExp = parse pExp


-- Testing

error-exp : Exp
error-exp = var "error"

parse! : Input → Exp
parse! s = case parseExp s of λ where
  (parsed e []) → e
  _ → error-exp

-- Examples

app-parsed : Result Exp
app-parsed = parseExp app-tokens

id-parsed : Result Exp
id-parsed = parseExp id-tokens

id-typed-parsed : Result Exp
id-typed-parsed = parseExp id-typed-tokens

one-parsed : Result Exp
one-parsed = parseExp one-tokens

one-par-parsed : Result Exp
one-par-parsed = parseExp one-par-tokens

K-parsed : Result Exp
K-parsed = parseExp K-tokens

S-parsed : Result Exp
S-parsed = parseExp S-tokens

zero-parsed : Result Exp
zero-parsed = parseExp zero-tokens

add-parsed : Result Exp
add-parsed = parseExp add-tokens

app-exp : Exp
app-exp = parse! app-tokens

id-exp : Exp
id-exp = parse! id-tokens

id-typed-exp : Exp
id-typed-exp = parse! id-typed-tokens

one-exp : Exp
one-exp = parse! one-tokens

one-par-exp : Exp
one-par-exp = parse! one-par-tokens

K-exp : Exp
K-exp = parse! K-tokens

S-exp : Exp
S-exp = parse! S-tokens

zero-exp : Exp
zero-exp = parse! zero-tokens

add-exp : Exp
add-exp = parse! add-tokens


-- -}
-- -}
-- -}
-- -}
