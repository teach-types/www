{-# OPTIONS --without-K --exact-split #-}

module minimalrules where

{-

 THE RULES WITHOUT THE REDUNDANT PREMISES, AND THE LEMMAS THEY COST

 This file is the companion of the four slides of lect6.tex which give the
 same theory with the redundant premises dropped, and of the slide "what the
 economy costs".  It contains

   -the MINIMAL rules, exactly as on the slides (PART 1)
   -the two translations between the minimal rules and those of typetype.agda (PARTS 3 and 4)
   -the lemmas of the last slide, for the MINIMAL system (PART 5):

        Γ ⊢ M : A   implies   ⊢ Γ   and   Γ ⊢ A : U
        Γ ⊢ M = N : A  implies  Γ ⊢ M : A  and  Γ ⊢ N : A
        weakening, and the substitution lemma

 WHY IT IS DONE THIS WAY.  One would like to prove the lemmas by induction on
 minimal-rule derivations.  This does NOT work, and it is instructive to see where it
 breaks: in the case of

         Γ, x:A ⊢ M : B
      ------------------------
       Γ ⊢ λ(x:A)M : Π(x:A)B

 the substitution lemma has to substitute in the context Γ, x:A, hence has to
 know Γ ⊢ A : U -- and that is the presupposition lemma, applied to a
 derivation which is NOT a subderivation of the one we are analysing.  The
 presupposition lemma in turn needs, in the case of application, that
 Γ ⊢ B[x/a] : U, which is the substitution lemma.  The two call each other on
 derivations of unrelated size: there is no structural induction, and no
 induction on the height of the derivations either.

 With the self-contained rules the circle is broken, because every premise one needs is
 a genuine subderivation: this is

     selfcontained.agda    (the rules of typetype.agda, then renaming,
                       substitution and presupposition, in one mutual
                       block, by structural induction; 0 postulates.
                       It is ~/DOMAIN/MIN/Syntax/{Raw,Typing,Substitution}
                       flattened into one self-contained file)

 So we do the honest thing: we prove that the two systems derive the same
 judgments -- the interesting direction, minimal to self-contained, is where the
 dropped premises are RECONSTRUCTED, using the presupposition lemma of the self-contained system
 -- and we then transport the lemmas to the minimal system.  This is exactly the
 argument of the slide, written out.

 To check this file: C-c C-l in emacs, or "agda minimalrules.agda".  The only
 thing it needs is selfcontained.agda, beside it in the same directory.

-}

open import selfcontained using (
  -- basic definitions
  Nat ; zero ; suc ; Pair ; mkSigma ; fst ; snd ; Eq ; refl ;
  -- raw syntax, renaming, substitution
  Fin ; fzero ; fsuc ; Expr ; Var ; U ; Pi ; Lam ; App ;
  liftRen ; wkRen ; renExpr ; wkExpr ; subst1 ;
  -- contexts and the self-contained rules
  Ctx ; empty ; extend ; lookup ;
  WfCtx ; wf-empty ; wf-extend ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  ConvTm ; conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  -- their metatheory (PART 5 of selfcontained.agda)
  typing-WfCtx ; typing-type ; typing-ConvTm ;
  wk-HasType ; subst-HasType ; subst1-WtSub ;
  ren-HasType ; wkRen-RenTypes ; liftRen-RenTypes ; subst1-liftWk-cancel)

-- ============================================================
-- PART 1.  The minimal rules
--
-- Same three judgments, same raw syntax, same contexts.  Only the
-- premises change: every premise which follows from the others is
-- gone.  Compare rule by rule with typetype.agda
-- ============================================================

data WfCtxM   : {n : Nat} -> Ctx n -> Set
data HasTypeM : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTmM  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

data WfCtxM where

 wfM-empty  : WfCtxM empty

 wfM-extend : {n : Nat} -> {G : Ctx n} -> {A : Expr n} ->
              HasTypeM G A U ->
              WfCtxM (extend G A)

data HasTypeM where

 -- unchanged: nothing here is redundant
 tyM-var : {n : Nat} -> {G : Ctx n} -> {i : Fin n} ->
           WfCtxM G ->
           HasTypeM G (Var i) (lookup G i)

 tyM-U : {n : Nat} -> {G : Ctx n} ->
         WfCtxM G ->
         HasTypeM G U U

 tyM-Pi : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
          HasTypeM G A U ->
          HasTypeM (extend G A) B U ->
          HasTypeM G (Pi A B) U

 --  Γ, x:A ⊢ M : B
 -- ------------------------
 --  Γ ⊢ λ(x:A)M : Π(x:A)B
 --
 -- A is a type because Γ, x:A is a context; B is one because M has type B
 tyM-Lam : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
           HasTypeM (extend G A) M B ->
           HasTypeM G (Lam A M) (Pi A B)

 --  Γ ⊢ f : Π(x:A)B    Γ ⊢ a : A
 -- -------------------------------
 --  Γ ⊢ f a : B[x/a]
 --
 -- A and B are read off the type of f
 tyM-App : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
           {f a : Expr n} ->
           HasTypeM G f (Pi A B) ->
           HasTypeM G a A ->
           HasTypeM G (App f a) (subst1 B a)

 --  Γ ⊢ M : A    Γ ⊢ A = B : U
 -- -----------------------------
 --  Γ ⊢ M : B
 --
 -- Γ ⊢ B : U is contained in the equation
 tyM-conv : {n : Nat} -> {G : Ctx n} -> {M A B : Expr n} ->
            HasTypeM G M A ->
            ConvTmM G A B U ->
            HasTypeM G M B

data ConvTmM where

 cvM-refl : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
            HasTypeM G M A ->
            ConvTmM G M M A

 cvM-sym : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
           ConvTmM G M N A ->
           ConvTmM G N M A

 cvM-trans : {n : Nat} -> {G : Ctx n} -> {M N P A : Expr n} ->
             ConvTmM G M N A ->
             ConvTmM G N P A ->
             ConvTmM G M P A

 cvM-conv : {n : Nat} -> {G : Ctx n} -> {M N A B : Expr n} ->
            ConvTmM G M N A ->
            ConvTmM G A B U ->
            ConvTmM G M N B

 --  Γ, x:A ⊢ M : B     Γ ⊢ a : A
 -- ------------------------------------------
 --  Γ ⊢ (λ(x:A)M) a = M[x/a] : B[x/a]
 cvM-beta : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
            {a : Expr n} ->
            HasTypeM (extend G A) M B ->
            HasTypeM G a A ->
            ConvTmM G (App (Lam A M) a) (subst1 M a) (subst1 B a)

 --  Γ ⊢ A = A' : U     Γ, x:A ⊢ B = B' : U
 -- -----------------------------------------
 --  Γ ⊢ Π(x:A)B = Π(x:A')B' : U
 cvM-Pi : {n : Nat} -> {G : Ctx n} -> {A A' : Expr n} -> {B B' : Expr (suc n)} ->
          ConvTmM G A A' U ->
          ConvTmM (extend G A) B B' U ->
          ConvTmM G (Pi A B) (Pi A' B') U

 --  Γ ⊢ f = f' : Π(x:A)B     Γ ⊢ a = a' : A
 -- -------------------------------------------
 --  Γ ⊢ f a = f' a' : B[x/a]
 --
 -- the two congruences of typetype.agda in one rule
 cvM-App : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
           {f f' a a' : Expr n} ->
           ConvTmM G f f' (Pi A B) ->
           ConvTmM G a a' A ->
           ConvTmM G (App f a) (App f' a') (subst1 B a)

 --  Γ ⊢ f : Π(x:A)B   Γ ⊢ g : Π(x:A)B   Γ, x:A ⊢ f x = g x : B
 -- --------------------------------------------------------------
 --  Γ ⊢ f = g : Π(x:A)B
 --
 -- here the two typings are NOT redundant: nothing in the third premise
 -- says that f and g are functions
 cvM-funext : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
              {f g : Expr n} ->
              HasTypeM G f (Pi A B) ->
              HasTypeM G g (Pi A B) ->
              ConvTmM (extend G A) (App (wkExpr f) (Var fzero))
                                   (App (wkExpr g) (Var fzero)) B ->
              ConvTmM G f g (Pi A B)

-- ============================================================
-- PART 2.  Two inversions in the self-contained system
--
-- Both are one line, by pattern matching: the shape of the conclusion
-- determines the last rule (for a type, up to a conversion step)
-- ============================================================

-- ⊢ Γ, x:A  gives  Γ ⊢ A : U
wf-tail : {n : Nat} -> {G : Ctx n} -> {A : Expr n} ->
          WfCtx (extend G A) -> HasType G A U
wf-tail (wf-extend dA) = dA

-- Γ ⊢ Π(x:A)B : T  gives  Γ ⊢ A : U  and  Γ, x:A ⊢ B : U
-- (the conversion case is where the type T is allowed to be anything)
ty-Pi-invert : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
               {T : Expr n} ->
               HasType G (Pi A B) T ->
               Pair (HasType G A U) (HasType (extend G A) B U)
ty-Pi-invert (ty-Pi dA dB)   = mkSigma dA dB
ty-Pi-invert (ty-conv d _ _) = ty-Pi-invert d

-- ============================================================
-- PART 3.  The minimal rules imply the others
--
-- This is the direction with content: the premises which the minimal rules
-- do not carry have to be RECONSTRUCTED.  They are produced by the
-- presupposition lemmas of the self-contained system,
--
--    typing-WfCtx : Γ ⊢ M : A  ->  ⊢ Γ
--    typing-type  : Γ ⊢ M : A  ->  Γ ⊢ A : U
--    typing-ConvTm: Γ ⊢ M = N : A  ->  Γ ⊢ M : A  and  Γ ⊢ N : A
--
-- proved in PART 5 of selfcontained.agda -- and by the two inversions
-- above.  The recursion is structural: on each minimal-rule derivation
-- ============================================================

toSelf-wf : {n : Nat} -> {G : Ctx n} -> WfCtxM G -> WfCtx G
toSelf-ty : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
           HasTypeM G M A -> HasType G M A
toSelf-cv : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
           ConvTmM G M N A -> ConvTm G M N A

toSelf-wf  wfM-empty      = wf-empty
toSelf-wf (wfM-extend dA) = wf-extend (toSelf-ty dA)

toSelf-ty (tyM-var wf)     = ty-var (toSelf-wf wf)
toSelf-ty (tyM-U wf)       = ty-U (toSelf-wf wf)
toSelf-ty (tyM-Pi dA dB)   = ty-Pi (toSelf-ty dA) (toSelf-ty dB)

-- Γ ⊢ A : U comes from the context of the premise, Γ, x:A ⊢ B : U from
-- the premise itself
toSelf-ty (tyM-Lam d)      = ty-Lam (wf-tail (typing-WfCtx d')) (typing-type d') d'
  where d' = toSelf-ty d

-- Γ ⊢ A : U and Γ, x:A ⊢ B : U are inside the type of f
toSelf-ty (tyM-App df da)  = ty-App (fst p) (snd p) df' (toSelf-ty da)
  where df' = toSelf-ty df
        p   = ty-Pi-invert (typing-type df')

-- Γ ⊢ B : U is the right-hand presupposition of the equation
toSelf-ty (tyM-conv d c)   = ty-conv (toSelf-ty d) c' (snd (typing-ConvTm c'))
  where c' = toSelf-cv c

toSelf-cv (cvM-refl d)       = conv-refl (toSelf-ty d)
toSelf-cv (cvM-sym c)        = conv-sym (toSelf-cv c)
toSelf-cv (cvM-trans c1 c2)  = conv-trans (toSelf-cv c1) (toSelf-cv c2)
toSelf-cv (cvM-conv c cAB)   = conv-conv (toSelf-cv c) cAB' (snd (typing-ConvTm cAB'))
  where cAB' = toSelf-cv cAB

toSelf-cv (cvM-beta d da)    = conv-beta (wf-tail (typing-WfCtx d')) (typing-type d')
                                        d' (toSelf-ty da)
  where d' = toSelf-ty d

toSelf-cv (cvM-Pi cA cB)     = conv-Pi (fst (typing-ConvTm cA')) (fst pB) (snd pB) cA' cB'
  where cA' = toSelf-cv cA
        cB' = toSelf-cv cB
        pB  = typing-ConvTm cB'

-- the single congruence becomes the two congruences of the self-contained system,
-- composed:  f a = f' a = f' a'
toSelf-cv (cvM-App cf ca)    = conv-trans (conv-App-fun dA dB cf' (fst pa))
                                         (conv-App-arg dA dB (snd pf) ca')
  where cf' = toSelf-cv cf
        ca' = toSelf-cv ca
        pf  = typing-ConvTm cf'
        pa  = typing-ConvTm ca'
        pAB = ty-Pi-invert (typing-type (fst pf))
        dA  = fst pAB
        dB  = snd pAB

toSelf-cv (cvM-funext df dg c) = conv-funext dA (toSelf-cv c) df' (toSelf-ty dg)
  where df' = toSelf-ty df
        dA  = fst (ty-Pi-invert (typing-type df'))

-- ============================================================
-- PART 4.  The others imply the minimal rules
--
-- Nothing to do: one forgets the extra premises.  The only case which
-- is not literally a forgetting is the pair of congruences for
-- application, which become the single minimal rule, the other argument
-- being related to itself by reflexivity
-- ============================================================

toMin-wf : {n : Nat} -> {G : Ctx n} -> WfCtx G -> WfCtxM G
toMin-ty : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
            HasType G M A -> HasTypeM G M A
toMin-cv : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
            ConvTm G M N A -> ConvTmM G M N A

toMin-wf  wf-empty       = wfM-empty
toMin-wf (wf-extend dA)  = wfM-extend (toMin-ty dA)

toMin-ty (ty-var wf)         = tyM-var (toMin-wf wf)
toMin-ty (ty-U wf)           = tyM-U (toMin-wf wf)
toMin-ty (ty-Pi dA dB)       = tyM-Pi (toMin-ty dA) (toMin-ty dB)
toMin-ty (ty-Lam _ _ d)      = tyM-Lam (toMin-ty d)
toMin-ty (ty-App _ _ df da)  = tyM-App (toMin-ty df) (toMin-ty da)
toMin-ty (ty-conv d c _)     = tyM-conv (toMin-ty d) (toMin-cv c)

toMin-cv (conv-refl d)              = cvM-refl (toMin-ty d)
toMin-cv (conv-sym c)               = cvM-sym (toMin-cv c)
toMin-cv (conv-trans c1 c2)         = cvM-trans (toMin-cv c1) (toMin-cv c2)
toMin-cv (conv-conv c cAB _)        = cvM-conv (toMin-cv c) (toMin-cv cAB)
toMin-cv (conv-beta _ _ d da)       = cvM-beta (toMin-ty d) (toMin-ty da)
toMin-cv (conv-Pi _ _ _ cA cB)      = cvM-Pi (toMin-cv cA) (toMin-cv cB)
toMin-cv (conv-funext _ c df dg)    = cvM-funext (toMin-ty df) (toMin-ty dg)
                                                  (toMin-cv c)
toMin-cv (conv-App-fun _ _ cf da)   = cvM-App (toMin-cv cf) (cvM-refl (toMin-ty da))
toMin-cv (conv-App-arg _ _ df ca)   = cvM-App (cvM-refl (toMin-ty df)) (toMin-cv ca)

-- ============================================================
-- PART 5.  The lemmas, for the minimal system
--
-- Each one is now: translate to the self-contained system, use the lemma there,
-- translate back
-- ============================================================

-- PRESUPPOSITION
--
--   Γ ⊢ M : A   implies   ⊢ Γ   and   Γ ⊢ A : U

presupM-ctx : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
              HasTypeM G M A -> WfCtxM G
presupM-ctx d = toMin-wf (typing-WfCtx (toSelf-ty d))

presupM-type : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
               HasTypeM G M A -> HasTypeM G A U
presupM-type d = toMin-ty (typing-type (toSelf-ty d))

--   Γ ⊢ M = N : A   implies   Γ ⊢ M : A   and   Γ ⊢ N : A
presupM-conv : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
               ConvTmM G M N A -> Pair (HasTypeM G M A) (HasTypeM G N A)
presupM-conv c = mkSigma (toMin-ty (fst p)) (toMin-ty (snd p))
  where p = typing-ConvTm (toSelf-cv c)

-- and hence also the type of a conversion is a type
presupM-conv-type : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
                    ConvTmM G M N A -> HasTypeM G A U
presupM-conv-type c = presupM-type (fst (presupM-conv c))

-- WEAKENING
--
--   Γ ⊢ C : U    Γ ⊢ M : A
--  --------------------------
--   Γ, x:C ⊢ M^ : A^

wkM : {n : Nat} -> {G : Ctx n} -> {C M A : Expr n} ->
      HasTypeM G C U ->
      HasTypeM G M A ->
      HasTypeM (extend G C) (wkExpr M) (wkExpr A)
wkM dC d = toMin-ty (wk-HasType (toSelf-ty dC) (toSelf-ty d))

-- SUBSTITUTION, in the form used by the rules: one variable
--
--   Γ, x:A ⊢ M : B     Γ ⊢ a : A
--  --------------------------------
--   Γ ⊢ M[x/a] : B[x/a]

substM : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
         {a : Expr n} ->
         HasTypeM (extend G A) M B ->
         HasTypeM G a A ->
         HasTypeM G (subst1 M a) (subst1 B a)
substM d da = toMin-ty (subst-HasType (subst1-WtSub dA da') (typing-WfCtx dA) d')
  where d'  = toSelf-ty d
        da' = toSelf-ty da
        dA  = wf-tail (typing-WfCtx d')

-- the special case which the application rule needs, and which was the
-- reason why the presupposition lemma could not be proved on its own
substM-type : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B : Expr (suc n)} ->
              {a : Expr n} ->
              HasTypeM (extend G A) B U ->
              HasTypeM G a A ->
              HasTypeM G (subst1 B a) U
substM-type dB da = substM dB da

-- ============================================================
-- PART 6.  What it buys: the xi rule, with nothing assumed
--
-- In xirule.agda the derivation of xi had to ASSUME the two instances
-- of the renaming lemma it needs.  Here they are theorems, so the
-- derivation is complete: the file proves what that one postulated
-- ============================================================

-- weakening under one binder: an expression of Γ, x:A becomes one of
-- Γ, x:A, y:A^
liftE : {n : Nat} -> Expr (suc n) -> Expr (suc (suc n))
liftE e = renExpr (liftRen wkRen) e

wk1M : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {M B : Expr (suc n)} ->
       HasTypeM G A U ->
       HasTypeM (extend G A) M B ->
       HasTypeM (extend (extend G A) (wkExpr A)) (liftE M) (liftE B)
wk1M {G = G} {A = A} dA d =
  toMin-ty (ren-HasType (liftRen-RenTypes (wkRen-RenTypes {G = G} {C = A}))
                         (wf-extend (wk-HasType dA' dA'))
                         (toSelf-ty d))
  where dA' = toSelf-ty dA

-- transport of a conversion along equalities of raw expressions
cvM-Eq : {n : Nat} -> {G : Ctx n} -> {M N N' A A' : Expr n} ->
         Eq N N' -> Eq A A' -> ConvTmM G M N A -> ConvTmM G M N' A'
cvM-Eq refl refl c = c

-- beta at the generic argument:  Γ, x:A ⊢ (λ(x:A)M)^ x = M : B
--
-- subst1-liftWk-cancel is the equation of PART 5 of xirule.agda:
-- weakening under the binder and substituting the variable back is the
-- identity
betaM-generic : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
                HasTypeM G A U ->
                HasTypeM (extend G A) M B ->
                ConvTmM (extend G A) (App (wkExpr (Lam A M)) (Var fzero)) M B
betaM-generic {B = B} {M = M} dA d =
  cvM-Eq (subst1-liftWk-cancel M) (subst1-liftWk-cancel B)
         (cvM-beta (wk1M dA d) (tyM-var (wfM-extend dA)))

-- and the rule itself
--
--     Γ, x:A ⊢ M = M' : B
--  -------------------------------------
--     Γ ⊢ λ(x:A)M = λ(x:A)M' : Π(x:A)B
--
-- note that the premises of xirule.agda -- the typings of M and M' --
-- are not needed here: they are presuppositions of the equation
xiM : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M M' : Expr (suc n)} ->
      ConvTmM (extend G A) M M' B ->
      ConvTmM G (Lam A M) (Lam A M') (Pi A B)
xiM c = cvM-funext (tyM-Lam dM) (tyM-Lam dM')
          (cvM-trans (betaM-generic dA dM)
                     (cvM-trans c (cvM-sym (betaM-generic dA dM'))))
  where p   = presupM-conv c
        dM  = fst p
        dM' = snd p
        -- the domain is a type, because Γ, x:A is a context
        dA  = toMin-ty (wf-tail (typing-WfCtx (toSelf-ty dM)))

-- ============================================================
-- PART 7.  The two systems, one theorem
--
-- The translations are total functions both ways, so a judgment has a
-- derivation with the minimal rules exactly when it has one with all the
-- premises.  Nothing is said about the SIZE of the derivations: toSelf-ty calls the
-- presupposition lemma, and the derivation it builds can be much bigger
-- ============================================================

equiv-ty : {n : Nat} -> {G : Ctx n} -> {M A : Expr n} ->
           Pair (HasTypeM G M A -> HasType G M A)
                (HasType G M A -> HasTypeM G M A)
equiv-ty = mkSigma toSelf-ty toMin-ty

equiv-cv : {n : Nat} -> {G : Ctx n} -> {M N A : Expr n} ->
           Pair (ConvTmM G M N A -> ConvTm G M N A)
                (ConvTm G M N A -> ConvTmM G M N A)
equiv-cv = mkSigma toSelf-cv toMin-cv

-- the self-contained rules, as admissible rules of the minimal system: one simply
-- does not use the extra premises
tyM-Lam-with-premises : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
              HasTypeM G A U ->
              HasTypeM (extend G A) B U ->
              HasTypeM (extend G A) M B ->
              HasTypeM G (Lam A M) (Pi A B)
tyM-Lam-with-premises _ _ d = tyM-Lam d

-- and, in the other direction, the premises the minimal rules do not carry
-- are derivable: this is PART 5 again
tyM-Lam-premises : {n : Nat} -> {G : Ctx n} -> {A : Expr n} -> {B M : Expr (suc n)} ->
                   HasTypeM (extend G A) M B ->
                   Pair (HasTypeM G A U) (HasTypeM (extend G A) B U)
tyM-Lam-premises d = mkSigma (toMin-ty (wf-tail (typing-WfCtx d'))) (presupM-type d)
  where d' = toSelf-ty d

-- ============================================================
-- PART 8.  What this file does not show
--
--  * that the minimal-rule derivation and the self-contained one have anything to do with
--    each other beyond deriving the same judgment: toMin-ty o toSelf-ty
--    is NOT the identity (it forgets and rebuilds the extra premises)
--
--  * a proof of the lemmas BY INDUCTION ON MINIMAL-RULE DERIVATIONS.  As
--    explained at the top, there is none of the usual kind: the
--    presupposition lemma and the substitution lemma call each other on
--    derivations of unrelated size.  What one can do -- and what this
--    file does -- is to prove them in a system where the induction is
--    structural, and transport
--
--  * this is why the presentations one finds in the literature keep a
--    few premises: Barendregt's pure type systems keep Γ ⊢ Π(x:A)B : s
--    in the abstraction rule and have weakening AS A RULE; the
--    Agda formalisation of Abel, Öhman and Vezzosi keeps the domain
--    typing in the rule for λ.  The extra premises are not clumsiness:
--    they are what makes the metatheory an induction
-- ============================================================
