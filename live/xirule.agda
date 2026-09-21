module xirule where

{-

 THE RULES, AND ONE DERIVATION: THE XI RULE

 This file is a companion of lect6.tex and of typetype.agda.  It contains

   -the rules of the theory, and nothing else (PARTS 1 to 4)
   -the derivation of the rule usually called XI (PARTS 6 and 7)

         Γ, x:A ⊢ M = M' : B
      -------------------------------------
         Γ ⊢ λ(x:A)M = λ(x:A)M' : Π(x:A)B

 The point of the slides was that this rule is NOT in the list: it is
 DERIVABLE from the beta rule and from function extensionality.  On paper
 the argument is three lines: apply the two functions to the generic
 argument x, use beta on each side to get M and M', and conclude by
 extensionality.  Here we write the same argument down completely.

 Two things which are invisible on paper have to be said in Agda:

   -"apply λ(x:A)M to the generic argument x" happens in the context
    Γ, x:A, so the term λ(x:A)M must first be WEAKENED.  The equation
    which makes the argument work is then

       subst1 (lift M) (Var fzero)  =  M

    "weaken under the binder, then substitute the variable back, is the
    identity".  It is proved in PART 5.

   -the premises of the beta rule are about the WEAKENED derivations.
    That weakening (renaming) is admissible -- a lemma about the rules,
    not a rule -- and we take it as given in PART 6.  PART 8 ends with
    a concrete instance of xi which assumes nothing at all.

-}

-- ============================================================
-- PART 1.  Raw syntax
-- ============================================================

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

data Fin : Nat -> Set where
 fzero : {n : Nat} -> Fin (suc n)
 fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

-- Expr n : the raw expressions with at most n free variables; no
-- distinction between terms and types, and Lam carries its domain
data Expr : Nat -> Set where
 Var : {n : Nat} -> Fin n -> Expr n
 U   : {n : Nat} -> Expr n
 Pi  : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
 Lam : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n
 App : {n : Nat} -> Expr n -> Expr n -> Expr n

-- ============================================================
-- PART 2.  Renaming and substitution
-- ============================================================

Ren : Nat -> Nat -> Set
Ren n m = Fin n -> Fin m

liftRen : {n m : Nat} -> Ren n m -> Ren (suc n) (suc m)
liftRen r  fzero    = fzero
liftRen r (fsuc i)  = fsuc (r i)

renExpr : {n m : Nat} -> Ren n m -> Expr n -> Expr m
renExpr r (Var i)    = Var (r i)
renExpr r  U         = U
renExpr r (Pi A B)   = Pi (renExpr r A) (renExpr (liftRen r) B)
renExpr r (Lam A M)  = Lam (renExpr r A) (renExpr (liftRen r) M)
renExpr r (App f a)  = App (renExpr r f) (renExpr r a)

wkRen : {n : Nat} -> Ren n (suc n)
wkRen i = fsuc i

-- weakening: an expression of Γ is one of Γ, x:A
wkExpr : {n : Nat} -> Expr n -> Expr (suc n)
wkExpr e = renExpr wkRen e

-- weakening UNDER ONE BINDER: an expression of Γ, x:A is one of
-- Γ, x:A, y:C.  This is the operation which appears in the beta rule
-- once the function has been weakened
liftE : {n : Nat} -> Expr (suc n) -> Expr (suc (suc n))
liftE e = renExpr (liftRen wkRen) e

Sub : Nat -> Nat -> Set
Sub h g = Fin g -> Expr h

idSub : {n : Nat} -> Sub n n
idSub i = Var i

liftSub : {h g : Nat} -> Sub h g -> Sub (suc h) (suc g)
liftSub s  fzero    = Var fzero
liftSub s (fsuc i)  = wkExpr (s i)

substExpr : {h g : Nat} -> Sub h g -> Expr g -> Expr h
substExpr s (Var i)    = s i
substExpr s  U         = U
substExpr s (Pi A B)   = Pi (substExpr s A) (substExpr (liftSub s) B)
substExpr s (Lam A M)  = Lam (substExpr s A) (substExpr (liftSub s) M)
substExpr s (App f a)  = App (substExpr s f) (substExpr s a)

subst1Sub : {n : Nat} -> Expr n -> Sub n (suc n)
subst1Sub a  fzero    = a
subst1Sub a (fsuc i)  = Var i

-- the B[a/x] of the slides
subst1 : {n : Nat} -> Expr (suc n) -> Expr n -> Expr n
subst1 B a = substExpr (subst1Sub a) B

-- ============================================================
-- PART 3.  Contexts
-- ============================================================

data Ctx : Nat -> Set where
 empty  : Ctx zero
 extend : {n : Nat} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Nat} -> Ctx n -> Fin n -> Expr n
lookup (extend G A)  fzero    = wkExpr A
lookup (extend G A) (fsuc i)  = wkExpr (lookup G i)

-- ============================================================
-- PART 4.  The rules
--
--    WfCtx G          "⊢ Γ"
--    HasType G M A    "Γ ⊢ M : A"
--    ConvTm G M N A   "Γ ⊢ M = N : A"
--
-- defined simultaneously; one constructor per rule of the slides
-- ============================================================

data WfCtx   : {n : Nat} -> Ctx n -> Set
data HasType : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

data WfCtx where

 wf-empty : WfCtx empty

 --  Γ ⊢ A : U
 -- -------------
 --  ⊢ Γ, x:A
 wf-extend : {n : Nat} -> {G : Ctx n} -> {A : Expr n} ->
             HasType G A U ->
             WfCtx (extend G A)

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
 --  Γ ⊢ U : U
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
 --  Γ ⊢ f a : B[a/x]
 ty-App : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
          {f a : Expr n} ->
          HasType G A U ->
          HasType (extend G A) B U ->
          HasType G f (Pi A B) ->
          HasType G a A ->
          HasType G (App f a) (subst1 B a)

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
 --  Γ ⊢ (λ(x:A)M) a = M[a/x] : B[a/x]
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
 conv-Pi : {n : Nat} -> {G : Ctx n} -> {A A' : Expr n} -> {B B' : Expr (suc n)} ->
           HasType G A U ->
           HasType (extend G A) B U ->
           HasType (extend G A) B' U ->
           ConvTm G A A' U ->
           ConvTm (extend G A) B B' U ->
           ConvTm G (Pi A B) (Pi A' B') U

 --  Γ ⊢ A : U   Γ, x:A ⊢ f x = g x : B   Γ ⊢ f : Π(x:A)B   Γ ⊢ g : Π(x:A)B
 -- --------------------------------------------------------------------------
 --  Γ ⊢ f = g : Π(x:A)B
 --
 -- "f x" in the context Γ, x:A is App (wkExpr f) (Var fzero)
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
 --  Γ ⊢ f a = f' a : B[a/x]
 conv-App-fun : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
                {f f' a : Expr n} ->
                HasType G A U ->
                HasType (extend G A) B U ->
                ConvTm G f f' (Pi A B) ->
                HasType G a A ->
                ConvTm G (App f a) (App f' a) (subst1 B a)

 --  Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ ⊢ f : Π(x:A)B   Γ ⊢ a = a' : A
 -- ----------------------------------------------------------------
 --  Γ ⊢ f a = f a' : B[a/x]
 conv-App-arg : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
                {f a a' : Expr n} ->
                HasType G A U ->
                HasType (extend G A) B U ->
                HasType G f (Pi A B) ->
                ConvTm G a a' A ->
                ConvTm G (App f a) (App f a') (subst1 B a)

-- ============================================================
-- PART 5.  One equation about substitution
--
-- Everything here is about RAW expressions: no rule is involved.  We
-- want the equation
--
--      subst1 (liftE M) (Var fzero)  =  M
--
-- which says that weakening M under a binder and then substituting the
-- variable back gives M again.  It is what makes "apply to the generic
-- argument and beta-reduce" give back M rather than something else.
--
-- We prove it with the equality type of lecture 5, and three lemmas,
-- each by induction on the expression.
-- ============================================================

data Eq {A : Set} (a : A) : A -> Set where
 refl : Eq a a

Eq-sym : {A : Set} -> {a b : A} -> Eq a b -> Eq b a
Eq-sym refl = refl

Eq-trans : {A : Set} -> {a b c : A} -> Eq a b -> Eq b c -> Eq a c
Eq-trans refl refl = refl

Eq-cong : {A B : Set} -> (f : A -> B) -> {a a' : A} -> Eq a a' -> Eq (f a) (f a')
Eq-cong f refl = refl

Eq-cong2 : {A B C : Set} -> (f : A -> B -> C) ->
           {a a' : A} -> {b b' : B} -> Eq a a' -> Eq b b' -> Eq (f a b) (f a' b')
Eq-cong2 f refl refl = refl

-- (1) two substitutions which agree pointwise have the same effect
liftSub-ext : {h g : Nat} -> (s s' : Sub h g) ->
              ((i : Fin g) -> Eq (s i) (s' i)) ->
              (i : Fin (suc g)) -> Eq (liftSub s i) (liftSub s' i)
liftSub-ext s s' p  fzero    = refl
liftSub-ext s s' p (fsuc i)  = Eq-cong wkExpr (p i)

substExpr-ext : {h g : Nat} -> (s s' : Sub h g) ->
                ((i : Fin g) -> Eq (s i) (s' i)) ->
                (e : Expr g) -> Eq (substExpr s e) (substExpr s' e)
substExpr-ext s s' p (Var i)    = p i
substExpr-ext s s' p  U         = refl
substExpr-ext s s' p (Pi A B)   =
  Eq-cong2 Pi (substExpr-ext s s' p A)
              (substExpr-ext (liftSub s) (liftSub s') (liftSub-ext s s' p) B)
substExpr-ext s s' p (Lam A M)  =
  Eq-cong2 Lam (substExpr-ext s s' p A)
               (substExpr-ext (liftSub s) (liftSub s') (liftSub-ext s s' p) M)
substExpr-ext s s' p (App f a)  =
  Eq-cong2 App (substExpr-ext s s' p f) (substExpr-ext s s' p a)

-- (2) the identity substitution does nothing
liftSub-id : {n : Nat} -> (i : Fin (suc n)) -> Eq (liftSub idSub i) (idSub i)
liftSub-id  fzero    = refl
liftSub-id (fsuc i)  = refl

substExpr-id : {n : Nat} -> (e : Expr n) -> Eq (substExpr idSub e) e
substExpr-id (Var i)    = refl
substExpr-id  U         = refl
substExpr-id (Pi A B)   =
  Eq-cong2 Pi (substExpr-id A)
              (Eq-trans (substExpr-ext (liftSub idSub) idSub liftSub-id B)
                        (substExpr-id B))
substExpr-id (Lam A M)  =
  Eq-cong2 Lam (substExpr-id A)
               (Eq-trans (substExpr-ext (liftSub idSub) idSub liftSub-id M)
                         (substExpr-id M))
substExpr-id (App f a)  = Eq-cong2 App (substExpr-id f) (substExpr-id a)

-- (3) a substitution after a renaming is a substitution
subst-ren-lift : {h n m : Nat} -> (s : Sub h m) -> (r : Ren n m) ->
                 (i : Fin (suc n)) ->
                 Eq (liftSub s (liftRen r i)) (liftSub (\ j -> s (r j)) i)
subst-ren-lift s r  fzero    = refl
subst-ren-lift s r (fsuc i)  = refl

subst-ren : {h n m : Nat} -> (s : Sub h m) -> (r : Ren n m) -> (e : Expr n) ->
            Eq (substExpr s (renExpr r e)) (substExpr (\ i -> s (r i)) e)
subst-ren s r (Var i)    = refl
subst-ren s r  U         = refl
subst-ren s r (Pi A B)   =
  Eq-cong2 Pi (subst-ren s r A)
              (Eq-trans (subst-ren (liftSub s) (liftRen r) B)
                        (substExpr-ext _ _ (subst-ren-lift s r) B))
subst-ren s r (Lam A M)  =
  Eq-cong2 Lam (subst-ren s r A)
               (Eq-trans (subst-ren (liftSub s) (liftRen r) M)
                         (substExpr-ext _ _ (subst-ren-lift s r) M))
subst-ren s r (App f a)  = Eq-cong2 App (subst-ren s r f) (subst-ren s r a)

-- the equation we are after
liftE-cancel-sub : {n : Nat} -> (i : Fin (suc n)) ->
                   Eq (subst1Sub {suc n} (Var fzero) (liftRen wkRen i)) (idSub i)
liftE-cancel-sub  fzero    = refl
liftE-cancel-sub (fsuc i)  = refl

liftE-cancel : {n : Nat} -> (e : Expr (suc n)) ->
               Eq (subst1 (liftE e) (Var fzero)) e
liftE-cancel e =
  Eq-trans (subst-ren (subst1Sub (Var fzero)) (liftRen wkRen) e)
           (Eq-trans (substExpr-ext _ idSub liftE-cancel-sub e)
                     (substExpr-id e))

-- transport of a conversion judgment along such equations
convEq : {n : Nat} -> {G : Ctx n} -> {M M' N N' A A' : Expr n} ->
         Eq M M' -> Eq N N' -> Eq A A' ->
         ConvTm G M N A -> ConvTm G M' N' A'
convEq refl refl refl d = d

-- ============================================================
-- PART 6.  Weakening, which is admissible
--
-- The beta rule has to be used in the context Γ, x:A, applied to the
-- WEAKENED function.  Its premises are then the weakened derivations,
-- and weakening is not a rule: it is an admissible rule, proved by
-- induction on derivations (it is ren-HasType in
-- ~/DOMAIN/MIN/Syntax/Substitution.agda, together with the analogous
-- statement for ConvTm).
--
-- It is orthogonal to the point of this file, so we take the two
-- instances we need as given.  They are the only assumptions here, and
-- the last derivation of PART 8 uses neither of them.
--
-- Both are THEOREMS in minimalrules.agda (wkM and wk1M there), which gets
-- them from the renaming lemma of selfcontained.agda; xi is derived there
-- too, with nothing assumed, as xiM.
--
--     Γ ⊢ C : U     Γ ⊢ M : A                Γ ⊢ C : U    Γ, x:C ⊢ M : A
--   ---------------------------------      ------------------------------------
--     Γ, x:C ⊢ M^ : A^                       Γ, x:C, y:C^ ⊢ M^ : A^
-- ============================================================

postulate
 wk-HasType  : {n : Nat} -> {G : Ctx n} -> {C M A : Expr n} ->
               HasType G C U ->
               HasType G M A ->
               HasType (extend G C) (wkExpr M) (wkExpr A)

 wk1-HasType : {n : Nat} -> {G : Ctx n} -> {C : Expr n} -> {M A : Expr (suc n)} ->
               HasType G C U ->
               HasType (extend G C) M A ->
               HasType (extend (extend G C) (wkExpr C)) (liftE M) (liftE A)

-- ============================================================
-- PART 7.  The xi rule, derived
--
--       Γ ⊢ A : U   Γ,x:A ⊢ B : U   Γ,x:A ⊢ M : B   Γ,x:A ⊢ M' : B
--                       Γ, x:A ⊢ M = M' : B
--      -------------------------------------------------------------
--                Γ ⊢ λ(x:A)M = λ(x:A)M' : Π(x:A)B
-- ============================================================

-- the generic argument: in the context Γ, x:A we have x : A^
tyGeneric : {n : Nat} -> {G : Ctx n} -> {A : Expr n} ->
            HasType G A U ->
            HasType (extend G A) (Var fzero) (wkExpr A)
tyGeneric dA = ty-var (wf-extend dA)

-- beta at the generic argument:  Γ, x:A ⊢ (λ(x:A)M)^ x = M : B
--
-- conv-beta gives the conversion with the right-hand side
-- subst1 (liftE M) (Var fzero) and the type subst1 (liftE B) (Var fzero);
-- the equation of PART 5 says that these ARE M and B
betaGeneric : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
              HasType G A U ->
              HasType (extend G A) B U ->
              HasType (extend G A) M B ->
              ConvTm (extend G A) (App (wkExpr (Lam A M)) (Var fzero)) M B
betaGeneric {B = B} {M = M} dA dB dM =
  convEq refl (liftE-cancel M) (liftE-cancel B)
         (conv-beta (wk-HasType dA dA)
                    (wk1-HasType dA dB)
                    (wk1-HasType dA dM)
                    (tyGeneric dA))

-- and here is the rule.  Three steps:
--   (λ(x:A)M)^ x  =  M  =  M'  =  (λ(x:A)M')^ x        in Γ, x:A
-- then function extensionality
xi : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M M' : Expr (suc n)} ->
     HasType G A U ->
     HasType (extend G A) B U ->
     HasType (extend G A) M B ->
     HasType (extend G A) M' B ->
     ConvTm (extend G A) M M' B ->
     ConvTm G (Lam A M) (Lam A M') (Pi A B)
xi dA dB dM dM' dconv =
  conv-funext dA
    (conv-trans (betaGeneric dA dB dM)
                (conv-trans dconv (conv-sym (betaGeneric dA dB dM'))))
    (ty-Lam dA dB dM)
    (ty-Lam dA dB dM')

-- ------------------------------------------------------------
-- The other rule the slides say we do not need: eta
--
--          Γ ⊢ f : Π(x:A)B
--      ------------------------------
--       Γ ⊢ f = λ(x:A)(f x) : Π(x:A)B
--
-- Same three steps.  The only new thing is that one must type the
-- generic application  Γ, x:A ⊢ f x : B,  which is where the equation
-- of PART 5 is used a second time
-- ------------------------------------------------------------

-- transport of a typing judgment, as convEq for conversion
tyEq : {n : Nat} -> {G : Ctx n} -> {M A A' : Expr n} ->
       Eq A A' -> HasType G M A -> HasType G M A'
tyEq refl d = d

-- Γ, x:A ⊢ f x : B
tyGenericApp : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
               {f : Expr n} ->
               HasType G A U ->
               HasType (extend G A) B U ->
               HasType G f (Pi A B) ->
               HasType (extend G A) (App (wkExpr f) (Var fzero)) B
tyGenericApp {B = B} dA dB df =
  tyEq (liftE-cancel B)
       (ty-App (wk-HasType dA dA) (wk1-HasType dA dB)
               (wk-HasType dA df) (tyGeneric dA))

etaRule : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
          {f : Expr n} ->
          HasType G A U ->
          HasType (extend G A) B U ->
          HasType G f (Pi A B) ->
          ConvTm G f (Lam A (App (wkExpr f) (Var fzero))) (Pi A B)
etaRule dA dB df =
  conv-funext dA
    (conv-sym (betaGeneric dA dB dfx))
    df
    (ty-Lam dA dB dfx)
  where dfx = tyGenericApp dA dB df

-- ============================================================
-- PART 8.  A concrete instance, assuming nothing
--
-- Take A = B = U and, in the context x:U,
--
--      M  =  (λ(y:U)y) x        M' =  x
--
-- so that M = M' : U by the beta rule, and xi should give
--
--      ⊢ λ(x:U)((λ(y:U)y) x)  =  λ(x:U)x  :  Π(x:U)U
--
-- Here every weakening is the identity on expressions (wkExpr U is U),
-- so the derivations of PART 6 are replaced by ty-U and ty-var: the
-- last derivation below, exXi', uses only the rules of PART 4 -- no
-- postulate, and not even the equation of PART 5
-- ============================================================

-- the contexts  ()  and  x:U  and  x:U, y:U
wf0 : WfCtx empty
wf0 = wf-empty

wf1 : WfCtx (extend empty U)
wf1 = wf-extend (ty-U wf0)

wf2 : WfCtx (extend (extend empty U) U)
wf2 = wf-extend (ty-U wf1)

-- x:U ⊢ U : U   and   x:U ⊢ x : U
tyU1 : HasType (extend empty U) U U
tyU1 = ty-U wf1

tyx : HasType (extend empty U) (Var fzero) U
tyx = ty-var wf1

-- x:U, y:U ⊢ U : U   and   x:U, y:U ⊢ y : U
tyU2 : HasType (extend (extend empty U) U) U U
tyU2 = ty-U wf2

tyy : HasType (extend (extend empty U) U) (Var fzero) U
tyy = ty-var wf2

-- x:U ⊢ (λ(y:U)y) x : U
tyM : HasType (extend empty U) (App (Lam U (Var fzero)) (Var fzero)) U
tyM = ty-App tyU1 tyU2 (ty-Lam tyU1 tyU2 tyy) tyx

-- x:U ⊢ (λ(y:U)y) x = x : U          -- one beta step
convM : ConvTm (extend empty U) (App (Lam U (Var fzero)) (Var fzero)) (Var fzero) U
convM = conv-beta tyU1 tyU2 tyy tyx

-- the instance of xi, obtained from the derived rule
exXi : ConvTm empty (Lam U (App (Lam U (Var fzero)) (Var fzero)))
                    (Lam U (Var fzero))
                    (Pi U U)
exXi = xi (ty-U wf0) tyU1 tyM tyx convM

-- and the same, written out with the rules only: this is the three line
-- argument of the slides, in this instance
--
--   x:U ⊢ (λ(x:U)((λ(y:U)y) x))^ x  =  (λ(y:U)y) x   by beta
--                                   =  x             by convM
--                                   =  (λ(x:U)x)^ x  by beta again
exXi' : ConvTm empty (Lam U (App (Lam U (Var fzero)) (Var fzero)))
                     (Lam U (Var fzero))
                     (Pi U U)
exXi' = conv-funext (ty-U wf0)
          (conv-trans (conv-beta tyU1 tyU2 (ty-App tyU2 (ty-U wf2') (ty-Lam tyU2 (ty-U wf2') tyy') tyy) tyx)
          (conv-trans convM
                      (conv-sym (conv-beta tyU1 tyU2 tyy tyx))))
          (ty-Lam (ty-U wf0) tyU1 tyM)
          (ty-Lam (ty-U wf0) tyU1 tyx)
 where
  wf2' : WfCtx (extend (extend (extend empty U) U) U)
  wf2' = wf-extend tyU2
  tyy' : HasType (extend (extend (extend empty U) U) U) (Var fzero) U
  tyy' = ty-var wf2'

-- ============================================================
-- PART 9.  Exercises
--
--  1. The rule xi is often stated without the premises Γ,x:A ⊢ M : B
--     and Γ,x:A ⊢ M' : B.  Where are they used above?  (Look at what
--     conv-funext asks for.)
--
--  2. Derive in the same way the congruence rule for Lam in which the
--     DOMAIN also changes:  from Γ ⊢ A = A' : U and Γ,x:A ⊢ M = M' : B,
--     derive Γ ⊢ λ(x:A)M = λ(x:A')M' : Π(x:A)B.
--
--  3. In etaRule, where exactly is the equation of PART 5 used, and for
--     which expression?  (There are two uses: find both.)
--
--  4. Replace the two postulates of PART 6 by a proof, for the special
--     case of the weakening renaming.  What else has to be proved at the
--     same time?  (Try it: this is how one discovers that renaming,
--     substitution and the presupposition lemma form one mutual
--     induction.)
-- ============================================================
