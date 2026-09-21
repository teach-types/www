module typetype where

{-

 THE RULES OF TYPE THEORY, WRITTEN DOWN

 This file is the companion of lect6.tex.  The slides give the rules in the
 usual informal notation

           Γ ⊢ A : U     Γ, x:A ⊢ B : U
          ------------------------------
              Γ ⊢ Π(x:A)B : U

 and this file gives EXACTLY the same rules as an inductive definition in
 Agda.  Reading the two side by side is the whole point: an inference rule
 is a constructor, a derivation is an element, and induction on derivations
 is pattern matching.

 The theory presented is the smallest interesting dependent type theory:

    -one type former, the dependent product Π(x:A)B
    -one universe U, with the rule U : U

 This is the fragment called "Type : Type".  It is INCONSISTENT as a logic
 (Girard's paradox, in the form given by Hurkens: there is a closed term of
 type Π(A:U)A).  We are not using it as a logic here; we use it because it
 is the smallest system in which all the phenomena of dependent types are
 already present -- and because, with U : U, there is no hierarchy of
 universes to carry around, so that the rules fit on two slides.

 The same rules, in the same shape, are what is implemented in
 ~/DOMAIN/MIN/Syntax/Raw.agda and ~/DOMAIN/MIN/Syntax/Typing.agda

-}

-- ============================================================
-- PART 1.  Raw syntax
-- ============================================================

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

-- Fin n has exactly n elements: the variables of a term with n free
-- variables (see deduction.agda, lecture 5)
data Fin : Nat -> Set where
 fzero : {n : Nat} -> Fin (suc n)
 fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

-- Expr n : the raw expressions with AT MOST n free variables
--
-- there is no distinction between terms and types: a type is an
-- expression, and "A is a type" will be the judgment  A : U
--
-- note that Lam carries its DOMAIN: we write λ(x:A)M, not λx.M
-- (so that a raw term determines the context of its body)
data Expr : Nat -> Set where
 Var : {n : Nat} -> Fin n -> Expr n
 U   : {n : Nat} -> Expr n
 Pi  : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
 Lam : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
 App : {n : Nat} -> Expr n -> Expr n -> Expr n

-- the binder is de Bruijn: in  Pi A B  the variable x of Π(x:A)B is
-- the index fzero of B, and B lives in Expr (suc n)
-- there are no variable names, hence no alpha-conversion to worry about

-- ============================================================
-- PART 2.  Renaming and substitution
--
-- Nothing conceptual here: this is the bookkeeping that makes the
-- notation B[x/a] of the slides precise.  It is written once and for
-- all, by structural recursion on the expression.
-- ============================================================

Ren : Nat -> Nat -> Set
Ren n m = Fin n -> Fin m

-- under a binder, a renaming must leave the new variable alone
liftRen : {n m : Nat} -> Ren n m -> Ren (suc n) (suc m)
liftRen r  fzero    = fzero
liftRen r (fsuc i)  = fsuc (r i)

renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)    = Var (r i)
renExpr r  U         = U
renExpr r (Pi A B)   = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (Lam A M)  = Lam (renExpr r A) (renExpr (liftRen r) M)
renExpr r (App f a)  = App (renExpr r f) (renExpr r a)

-- weakening: an expression of the context Γ is one of the context Γ, x:A
wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr fsuc e

-- a substitution gives an expression for each variable
Sub : Nat -> Nat -> Set
Sub h g = Fin g -> Expr h

liftSub : {h g : Nat} -> Sub h g -> Sub (suc h) (suc g)
liftSub s  fzero    = Var fzero
liftSub s (fsuc i)  = wkExpr (s i)

substExpr : {h g : Nat} -> Sub h g -> Expr g -> Expr h
substExpr s (Var i)    = s i
substExpr s  U         = U
substExpr s (Pi A B)   = Pi (substExpr s A) (substExpr (liftSub s) B)
substExpr s (Lam A M)  = Lam (substExpr s A) (substExpr (liftSub s) M)
substExpr s (App f a)  = App (substExpr s f) (substExpr s a)

-- substituting the ONE variable fzero: this is the B[x/a] of the slides
subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub a  fzero    = a
subst1Sub a (fsuc i)  = Var i

subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 B a = substExpr (subst1Sub a) B

-- ============================================================
-- PART 3.  Contexts
-- ============================================================

-- a context is a list of types, written from the left: Γ, x:A
-- its length is the number of free variables available
data Ctx : Nat -> Set where
 empty  : Ctx zero
 extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

-- the type of a variable, WEAKENED so as to live in the whole context:
-- if Γ = Γ0, x:A then the type of x is A weakened by one
lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A)  fzero    = wkExpr A
lookup (extend G A) (fsuc i)  = wkExpr (lookup G i)

-- ============================================================
-- PART 4.  The three judgments
--
--    WfCtx G          "⊢ Γ"            Γ is a well formed context
--    HasType G M A    "Γ ⊢ M : A"      M has type A in Γ
--    ConvTm G M N A   "Γ ⊢ M = N : A"  M and N are convertible at type A
--
-- They are defined MUTUALLY: a context is well formed when its types
-- are of type U, and conversion occurs among the premises of typing.
--
-- There is NO fourth judgment "Γ ⊢ A type": with U : U, being a type
-- is simply being of type U.  Likewise there is no separate judgment
-- of type equality: it is conversion at the type U.
-- ============================================================

data WfCtx   : {n : Nat} -> Ctx n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

-- ------------------------------------------------------------
-- Well formed contexts
-- ------------------------------------------------------------

data WfCtx where

 --
 -- ---------
 --  ⊢ ()
 wf-empty : WfCtx empty

 --  Γ ⊢ A : U
 -- -------------
 --  ⊢ Γ, x:A
 wf-extend : {n : Nat} -> {G : Ctx n} -> {A : Expr n} ->
             HasType G A U ->
             WfCtx (extend G A)

-- ------------------------------------------------------------
-- Typing
-- ------------------------------------------------------------

data HasType where

 --  ⊢ Γ        (x:A in Γ)
 -- ------------
 --  Γ ⊢ x : A
 ty-var : {n : Nat} -> {G : Ctx n} -> {i : Fin n} ->
          WfCtx G ->
          HasType G (Var i) (lookup G i)

 --  Γ ⊢ M : A    Γ ⊢ A = B : U    Γ ⊢ B : U
 -- ------------------------------------------
 --  Γ ⊢ M : B
 ty-conv : {n : Nat} -> {G : Ctx n} -> {M A B : Expr n} ->
           HasType G M A ->
           ConvTm G A B U ->
           HasType G B U ->
           HasType G M B

 --  ⊢ Γ
 -- ------------
 --  Γ ⊢ U : U          <- THE rule of this theory
 ty-U : {n : Nat} -> {G : Ctx n} ->
        WfCtx G ->
        HasType G U U

 --  Γ ⊢ A : U     Γ, x:A ⊢ B : U
 -- ------------------------------
 --  Γ ⊢ Π(x:A)B : U
 ty-Pi : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
         HasType G A U ->
         HasType (extend G A) B U ->
         HasType G (Pi A B) U

 --  Γ ⊢ A : U     Γ, x:A ⊢ B : U     Γ, x:A ⊢ M : B
 -- -------------------------------------------------
 --  Γ ⊢ λ(x:A)M : Π(x:A)B
 ty-Lam : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
          HasType G A U ->
          HasType (extend G A) B U ->
          HasType (extend G A) M B ->
          HasType G (Lam A M) (Pi A B)

 --  Γ ⊢ A : U   Γ, x:A ⊢ B : U   Γ ⊢ f : Π(x:A)B   Γ ⊢ a : A
 -- -----------------------------------------------------------
 --  Γ ⊢ f a : B[x/a]
 ty-App : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
          {f a : Expr n} ->
          HasType G A U ->
          HasType (extend G A) B U ->
          HasType G f (Pi A B) ->
          HasType G a A ->
          HasType G (App f a) (subst1 B a)

-- ------------------------------------------------------------
-- Conversion
--
-- Conversion is a judgment, NOT a relation on raw terms: it is typed,
-- and it relates only well typed terms.  This is why conv-refl takes
-- a typing derivation as premise.
-- ------------------------------------------------------------

data ConvTm where

 --  Γ ⊢ M : A
 -- ---------------
 --  Γ ⊢ M = M : A
 conv-refl : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
             HasType G M A ->
             ConvTm G M M A

 conv-sym : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
            ConvTm G M N A ->
            ConvTm G N M A

 conv-trans : {n : Nat} -> {G : Ctx n} -> {M N P A : Expr n} ->
              ConvTm G M N A ->
              ConvTm G N P A ->
              ConvTm G M P A

 --  Γ ⊢ M = N : A    Γ ⊢ A = B : U    Γ ⊢ B : U
 -- ----------------------------------------------
 --  Γ ⊢ M = N : B
 conv-conv : {n : Nat} -> {G : Ctx n} -> {M N A B : Expr n} ->
             ConvTm G M N A ->
             ConvTm G A B U ->
             HasType G B U ->
             ConvTm G M N B

 --  Γ ⊢ A : U   Γ, x:A ⊢ B : U   Γ, x:A ⊢ M : B   Γ ⊢ a : A
 -- ----------------------------------------------------------
 --  Γ ⊢ (λ(x:A)M) a = M[x/a] : B[x/a]              <- the beta rule
 conv-beta : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
             {a : Expr n} ->
             HasType G A U ->
             HasType (extend G A) B U ->
             HasType (extend G A) M B ->
             HasType G a A ->
             ConvTm G (App (Lam A M) a) (subst1 M a) (subst1 B a)

 --  Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ,x:A ⊢ B' : U
 --  Γ ⊢ A = A' : U      Γ, x:A ⊢ B = B' : U
 -- ---------------------------------------------
 --  Γ ⊢ Π(x:A)B = Π(x:A')B' : U
 --
 -- the first three premises are the typings of the three components;
 -- they are redundant (they follow from the two conversions) but they
 -- are put in the rule on purpose, see the note at the end of the file
 conv-Pi : {n : Nat} -> {G : Ctx n} -> {A A' : Expr n} -> {B B' : Expr (suc n)} ->
           HasType G A U ->
           HasType (extend G A) B U ->
           HasType (extend G A) B' U ->
           ConvTm G A A' U ->
           ConvTm (extend G A) B B' U ->
           ConvTm G (Pi A B) (Pi A' B') U

 --  Γ ⊢ A : U   Γ, x:A ⊢ f x = g x : B   Γ ⊢ f : Π(x:A)B   Γ ⊢ g : Π(x:A)B
 -- --------------------------------------------------------------------------
 --  Γ ⊢ f = g : Π(x:A)B                       <- function extensionality
 --
 -- two functions are equal when they are equal at the generic argument
 -- (wkExpr f applied to Var fzero IS "f x" in the context Γ, x:A)
 conv-funext : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
               {f g : Expr n} ->
               HasType G A U ->
               ConvTm (extend G A) (App (wkExpr f) (Var fzero))
                                   (App (wkExpr g) (Var fzero)) B ->
               HasType G f (Pi A B) ->
               HasType G g (Pi A B) ->
               ConvTm G f g (Pi A B)

 --  Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ f = f' : Π(x:A)B   Γ ⊢ a : A
 -- ----------------------------------------------------------------
 --  Γ ⊢ f a = f' a : B[x/a]
 conv-App-fun : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
                {f f' a : Expr n} ->
                HasType G A U ->
                HasType (extend G A) B U ->
                ConvTm G f f' (Pi A B) ->
                HasType G a A ->
                ConvTm G (App f a) (App f' a) (subst1 B a)

 --  Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ f : Π(x:A)B   Γ ⊢ a = a' : A
 -- ----------------------------------------------------------------
 --  Γ ⊢ f a = f a' : B[x/a]
 conv-App-arg : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
                {f a a' : Expr n} ->
                HasType G A U ->
                HasType (extend G A) B U ->
                HasType G f (Pi A B) ->
                ConvTm G a a' A ->
                ConvTm G (App f a) (App f a') (subst1 B a)

-- ============================================================
-- PART 5.  That is all.
--
-- Twelve rules for conversion and typing, two for contexts.  Every
-- question of the form "is this a rule of type theory?" can now be
-- answered by looking at the list above.
--
-- Three things are NOT there, and it is worth saying so out loud:
--
--   * no rule  Γ ⊢ λ(x:A)M = λ(x:A)M' : Π(x:A)B  from  Γ,x:A ⊢ M = M' : B
--     (the rule usually called xi).  It is DERIVABLE from conv-funext
--     and conv-beta: apply both sides to the generic argument x and
--     use beta twice.
--
--   * no eta rule  f = λ(x:A) f x  as such; conv-funext plays its role.
--
--   * no reduction relation.  Conversion is defined directly, as a
--     judgment; reduction (~/DOMAIN/MIN/Syntax/Reduction.agda) is a
--     separate notion, used to STUDY the theory, not to define it.
-- ============================================================

-- ============================================================
-- PART 6.  A derivation, in full
--
-- The polymorphic identity, in the theory:
--
--    λ(A:U) λ(x:A) x   :   Π(A:U) Π(x:A) A
--
-- In de Bruijn notation the type is  Pi U (Pi (Var 0) (Var 1)):
-- inside the second Pi, the variable A is one binder further away.
-- ============================================================

idTerm : Expr zero
idTerm = Lam U (Lam (Var fzero) (Var fzero))

idType : Expr zero
idType = Pi U (Pi (Var fzero) (Var (fsuc fzero)))

-- the context  A:U
G1 : Ctx (suc zero)
G1 = extend empty U

-- the context  A:U, x:A
G2 : Ctx (suc (suc zero))
G2 = extend G1 (Var fzero)

wf1 : WfCtx G1
wf1 = wf-extend (ty-U wf-empty)

-- A:U ⊢ A : U     (lookup G1 fzero is U, weakened, which IS U)
tyA : HasType G1 (Var fzero) U
tyA = ty-var wf1

wf2 : WfCtx G2
wf2 = wf-extend tyA

-- A:U, x:A ⊢ A : U   (the weakening of the previous one)
tyA2 : HasType G2 (Var (fsuc fzero)) U
tyA2 = ty-var wf2

-- A:U, x:A ⊢ x : A
tyx : HasType G2 (Var fzero) (Var (fsuc fzero))
tyx = ty-var wf2

-- A:U ⊢ Π(x:A)A : U
tyPiA : HasType G1 (Pi (Var fzero) (Var (fsuc fzero))) U
tyPiA = ty-Pi tyA tyA2

-- A:U ⊢ λ(x:A)x : Π(x:A)A
tyInner : HasType G1 (Lam (Var fzero) (Var fzero)) (Pi (Var fzero) (Var (fsuc fzero)))
tyInner = ty-Lam tyA tyA2 tyx

-- and finally the whole thing
tyId : HasType empty idTerm idType
tyId = ty-Lam (ty-U wf-empty) tyPiA tyInner

-- ------------------------------------------------------------
-- The same identity, applied to U itself -- which is legal here
-- precisely because U : U
--
--    (λ(A:U) λ(x:A) x) U  :  Π(x:U)U
--
-- and beta says this is convertible to λ(x:U)x
-- ------------------------------------------------------------

tyIdU : HasType empty (App idTerm U) (Pi U U)
tyIdU = ty-App (ty-U wf-empty) tyPiA tyId (ty-U wf-empty)

betaIdU : ConvTm empty (App idTerm U) (Lam U (Var fzero)) (Pi U U)
betaIdU = conv-beta (ty-U wf-empty) tyPiA tyInner (ty-U wf-empty)

-- note the types: Agda computes subst1 (Pi (Var 0) (Var 1)) U to Pi U U
-- and subst1 (Lam (Var 0) (Var 0)) U to Lam U (Var 0), so these two
-- declarations typecheck AS WRITTEN: the substitutions of the rules are
-- carried out by the same machinery we defined in PART 2

-- ============================================================
-- PART 7.  Why so many premises?
--
-- Several premises above are redundant: in ty-App, the premises
-- Γ ⊢ A : U and Γ, x:A ⊢ B : U follow from Γ ⊢ f : Π(x:A)B.  One CAN
-- state the rules without them.  The price is that one then has to
-- prove a "presupposition" lemma -- if Γ ⊢ M : A then Γ ⊢ A : U and
-- ⊢ Γ -- BEFORE being able to do induction on derivations, and that
-- lemma is itself proved by induction on derivations, so the whole
-- development becomes a large mutual induction.
--
-- Carrying the premises makes every rule self-contained: each piece of
-- data one needs is a genuine SUBDERIVATION, so a function defined by
-- induction on derivations (for instance the interpretation into a
-- model) is structurally recursive, and Agda accepts it directly.
-- The cost is that derivations are bigger; the benefit is that all the
-- proofs about them go through.
-- ============================================================
