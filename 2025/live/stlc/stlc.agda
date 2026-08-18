module stlc where

open import Prelude
open import Prelude.IO

open import Lexer  using (lex)
open import Parser using (parseExp; parsed; failed)
open import Term
open import NatSignature -- using (scopeℕ)
open import Check  using (infer; inferred; failed; prettyCheckError)


check : String → IO ⊤
check s =
  case parseExp (lex s) of λ where
    (failed err) → parseError
    (parsed e _) →
      case infer scopeℕ e of λ where
        (failed err) → typeError err
        (inferred tℕ t) → putStrLn (ℕ.show (evalℕ t))
        (inferred Chℕ t) → putStrLn (ℕ.show (evalℕ (app (app t (var zero)) (var (suc zero)))))
        _ → unexpectedType
  where
  open IOMonad
  parseError = do
    putStrLn "PARSE ERROR"
    exitFailure
  typeError = λ err → do
    putStrLn "TYPE ERROR"
    putStrLn (prettyCheckError err)
    exitFailure
  unexpectedType = do
    putStrLn "ERROR: expected expression of type ℕ or (ℕ → ℕ) → ℕ → ℕ"
    exitFailure

-- Display usage information and exit

usage : IO ⊤
usage = do
  putStrLn "Usage: stlc <SourceFile>"
  exitFailure
  where open IOMonad

-- Parse command line argument and pass file contents to check.

main : IO ⊤
main = do
  file ∷ [] ← getArgs where _ → usage
  check =<< readFiniteFile file
  where open IOMonad
