{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Confluence
--
-- The Church-Rosser theorem for beta-reduction on the raw syntax
-- `Expr n`, following Barendregt's thesis, Appendix II ("The
-- Church-Rosser theorem for the lambda-calculus a la Martin-Loef",
-- pp. 128-133), i.e. the Tait / Martin-Loef parallel-reduction proof.
--
-- The terms are those of the rules of Type : Type (selfcontained.agda):
-- besides variables, application and abstraction there are `U` and
-- `Pi A B`, and an abstraction `Lam A M` carries the type A of its
-- variable.  The paper is about the pure lambda-calculus; the extra
-- term formers only add congruence cases, which go exactly like the
-- case of lambda.
--
-- The correspondence with the paper:
--
--   paper                          here
--   -----------------------------  ------------------------------------
--   >= 1  (one step reduction)     Par        (parallel reduction)
--   >=    (reduction)              Beta       (many step beta reduction)
--   =     (convertibility)         Conv
--   Lemma 3                        by construction (ParStar IS the
--                                  transitive closure of Par)
--   Lemma 4                        beta1-Par / Par-Beta / Beta-ParStar
--                                  / ParStar-Beta
--   Lemma 5                        Par-subst, Par-subst1
--   Lemma 6  (inversion of >= 1)   pattern matching (no lemma needed)
--   Lemma 7  (the diamond for >=1) Par-diamond
--   Lemma 8  (figure 2, page 40)   Par-strip, ParStar-diamond,
--                                  Beta-confluent
--   Lemma 9                        Conv-common
--   Theorem 10                     church-rosser
--
-- and, as the two corollaries the theorem exists for:
--
--  * beta conversion (`BConv`: having a common reduct) is an
--    equivalence relation, its transitivity being precisely the
--    Church-Rosser theorem;
--  * normal forms are unique (`NF-unique`);
--  * Pi is injective for beta conversion (`Pi-inj`), with the companion
--    `Conv-U-Pi` (a universe is never convertible to a product).
--
-- Two features of the paper's presentation disappear here, because the
-- syntax is de Bruijn (`Expr n` over `Fin n`) rather than named:
--
--  * The paper's rule I.1  (M >=1 M'  =>  \xM >=1 \y[x/y]M', y notin
--    FV(M')) is alpha-conversion built into the relation.  Here alpha
--    equivalence is `Eq`, so I.1 collapses into the congruence rule
--    `par-Lam`, and case 2 of Lemma 7 becomes case 3.
--  * The side condition BV(M') cap FV(N') = 0 on the beta rule I.2 is
--    an artifact of naive named substitution.  `substExpr` is
--    capture-avoiding by construction, so `par-beta` has no side
--    condition.
--
-- Also, Lemma 7 is proved here by structural recursion on the two
-- derivations, not on "the sum of the lengths of proof".
--
-- This module depends only on selfcontained.agda, for the syntax, the
-- substitution and `subst-subst1-comm`, the de Bruijn form of the
-- sublemma of the paper's Lemma 5.  It uses no typing rules, no
-- postulates, no pragmas and no `with`: `Sigma` is a record
-- with eta, so every case that would use `with` uses instead a `let`
-- binding with an irrefutable record pattern.
------------------------------------------------------------------------

module Confluence where

open import selfcontained using (Nat ; suc ; Eq ; refl ; Eq-sym ;
  Eq-transport ; Sigma ; mkSigma ; Pair ;
  Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Pi ; Lam ; App ;
  Ren ; liftRen ; renExpr ; wkRen ; wkExpr ;
  Sub ; liftSub ; substExpr ; subst1Sub ; subst1 ;
  Eq-trans ; Eq-cong2-Expr ; substExpr-ext ; subst-ren ; ren-subst ;
  subst-subst1-comm)

-- The empty type (not exported by selfcontained.agda).
data Empty : Set where

------------------------------------------------------------------------
-- Part 0.  One auxiliary equality
--
-- `subst-subst1-comm` is proved in selfcontained.agda; its analogue
-- for a renaming is proved here.
------------------------------------------------------------------------

ren-subst1 : {n m : Nat} (r : Ren n m) (B : Expr (suc n)) (a : Expr n) ->
  Eq (renExpr r (subst1 B a)) (subst1 (renExpr (liftRen r) B) (renExpr r a))
ren-subst1 r B a =
  Eq-trans (ren-subst r (subst1Sub a) B)
    (Eq-trans (substExpr-ext _ _ ext B)
      (Eq-sym (subst-ren (subst1Sub (renExpr r a)) (liftRen r) B)))
  where
    ext : (i : Fin _) ->
      Eq (renExpr r (subst1Sub a i))
         (subst1Sub (renExpr r a) (liftRen r i))
    ext fzero    = refl
    ext (fsuc i) = refl

------------------------------------------------------------------------
-- Part 1.  Beta reduction and convertibility  (the paper's lambda)
------------------------------------------------------------------------

-- One step beta reduction, compatible with every term former.
data Beta1 : {n : Nat} -> Expr n -> Expr n -> Set where
  beta      : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
              Beta1 (App (Lam A M) N) (subst1 M N)
  beta-Pi1  : {n : Nat} {A A' : Expr n} {B : Expr (suc n)} ->
              Beta1 A A' -> Beta1 (Pi A B) (Pi A' B)
  beta-Pi2  : {n : Nat} {A : Expr n} {B B' : Expr (suc n)} ->
              Beta1 B B' -> Beta1 (Pi A B) (Pi A B')
  beta-Lam1 : {n : Nat} {A A' : Expr n} {M : Expr (suc n)} ->
              Beta1 A A' -> Beta1 (Lam A M) (Lam A' M)
  beta-Lam2 : {n : Nat} {A : Expr n} {M M' : Expr (suc n)} ->
              Beta1 M M' -> Beta1 (Lam A M) (Lam A M')
  beta-App1 : {n : Nat} {M M' N : Expr n} ->
              Beta1 M M' -> Beta1 (App M N) (App M' N)
  beta-App2 : {n : Nat} {M N N' : Expr n} ->
              Beta1 N N' -> Beta1 (App M N) (App M N')

-- Many step beta reduction: the reflexive transitive closure.
data Beta : {n : Nat} -> Expr n -> Expr n -> Set where
  beta-refl : {n : Nat} {M : Expr n} -> Beta M M
  beta-step : {n : Nat} {M N P : Expr n} ->
              Beta1 M N -> Beta N P -> Beta M P

Beta-trans : {n : Nat} {M N P : Expr n} -> Beta M N -> Beta N P -> Beta M P
Beta-trans beta-refl        r2 = r2
Beta-trans (beta-step s r1) r2 = beta-step s (Beta-trans r1 r2)

Beta-one : {n : Nat} {M N : Expr n} -> Beta1 M N -> Beta M N
Beta-one s = beta-step s beta-refl

-- Convertibility: the paper's lambda, i.e. the equivalence relation
-- generated by beta and closed under the term formers.
data Conv : {n : Nat} -> Expr n -> Expr n -> Set where
  conv-beta  : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
               Conv (App (Lam A M) N) (subst1 M N)
  conv-refl  : {n : Nat} {M : Expr n} -> Conv M M
  conv-sym   : {n : Nat} {M N : Expr n} -> Conv M N -> Conv N M
  conv-trans : {n : Nat} {M N P : Expr n} -> Conv M N -> Conv N P -> Conv M P
  conv-Pi    : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
               Conv A A' -> Conv B B' -> Conv (Pi A B) (Pi A' B')
  conv-Lam   : {n : Nat} {A A' : Expr n} {M M' : Expr (suc n)} ->
               Conv A A' -> Conv M M' -> Conv (Lam A M) (Lam A' M')
  conv-App   : {n : Nat} {M M' N N' : Expr n} ->
               Conv M M' -> Conv N N' -> Conv (App M N) (App M' N')

------------------------------------------------------------------------
-- Part 2.  Beta is a congruence
------------------------------------------------------------------------

Beta-Pi1 : {n : Nat} {A A' : Expr n} {B : Expr (suc n)} ->
  Beta A A' -> Beta (Pi A B) (Pi A' B)
Beta-Pi1 beta-refl       = beta-refl
Beta-Pi1 (beta-step s r) = beta-step (beta-Pi1 s) (Beta-Pi1 r)

Beta-Pi2 : {n : Nat} {A : Expr n} {B B' : Expr (suc n)} ->
  Beta B B' -> Beta (Pi A B) (Pi A B')
Beta-Pi2 beta-refl       = beta-refl
Beta-Pi2 (beta-step s r) = beta-step (beta-Pi2 s) (Beta-Pi2 r)

Beta-Pi : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  Beta A A' -> Beta B B' -> Beta (Pi A B) (Pi A' B')
Beta-Pi rA rB = Beta-trans (Beta-Pi1 rA) (Beta-Pi2 rB)

Beta-Lam1 : {n : Nat} {A A' : Expr n} {M : Expr (suc n)} ->
  Beta A A' -> Beta (Lam A M) (Lam A' M)
Beta-Lam1 beta-refl       = beta-refl
Beta-Lam1 (beta-step s r) = beta-step (beta-Lam1 s) (Beta-Lam1 r)

Beta-Lam2 : {n : Nat} {A : Expr n} {M M' : Expr (suc n)} ->
  Beta M M' -> Beta (Lam A M) (Lam A M')
Beta-Lam2 beta-refl       = beta-refl
Beta-Lam2 (beta-step s r) = beta-step (beta-Lam2 s) (Beta-Lam2 r)

Beta-Lam : {n : Nat} {A A' : Expr n} {M M' : Expr (suc n)} ->
  Beta A A' -> Beta M M' -> Beta (Lam A M) (Lam A' M')
Beta-Lam rA rM = Beta-trans (Beta-Lam1 rA) (Beta-Lam2 rM)

Beta-App1 : {n : Nat} {M M' N : Expr n} ->
  Beta M M' -> Beta (App M N) (App M' N)
Beta-App1 beta-refl       = beta-refl
Beta-App1 (beta-step s r) = beta-step (beta-App1 s) (Beta-App1 r)

Beta-App2 : {n : Nat} {M N N' : Expr n} ->
  Beta N N' -> Beta (App M N) (App M N')
Beta-App2 beta-refl       = beta-refl
Beta-App2 (beta-step s r) = beta-step (beta-App2 s) (Beta-App2 r)

Beta-App : {n : Nat} {M M' N N' : Expr n} ->
  Beta M M' -> Beta N N' -> Beta (App M N) (App M' N')
Beta-App rM rN = Beta-trans (Beta-App1 rM) (Beta-App2 rN)

------------------------------------------------------------------------
-- Part 3.  Parallel reduction  (the paper's >= 1, Definition 2)
--
-- Rule I.1 of the paper is absorbed into par-Lam, and the side
-- condition of I.2 into the definition of substExpr.  Rule II.1
-- (M >=1 M for arbitrary M) is derived below as `par-refl` rather than
-- postulated, which keeps inversion (the paper's Lemma 6) exact.
------------------------------------------------------------------------

data Par : {n : Nat} -> Expr n -> Expr n -> Set where
  par-var  : {n : Nat} {i : Fin n} -> Par (Var i) (Var i)
  par-U    : {n : Nat} -> Par {n} U U
  par-Pi   : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
             Par A A' -> Par B B' -> Par (Pi A B) (Pi A' B')
  par-Lam  : {n : Nat} {A A' : Expr n} {M M' : Expr (suc n)} ->
             Par A A' -> Par M M' -> Par (Lam A M) (Lam A' M')
  par-App  : {n : Nat} {M M' N N' : Expr n} ->
             Par M M' -> Par N N' -> Par (App M N) (App M' N')
  par-beta : {n : Nat} {A : Expr n} {M M' : Expr (suc n)} {N N' : Expr n} ->
             Par M M' -> Par N N' -> Par (App (Lam A M) N) (subst1 M' N')

par-refl : {n : Nat} (M : Expr n) -> Par M M
par-refl (Var i)   = par-var
par-refl U         = par-U
par-refl (Pi A B)  = par-Pi (par-refl A) (par-refl B)
par-refl (Lam A M) = par-Lam (par-refl A) (par-refl M)
par-refl (App M N) = par-App (par-refl M) (par-refl N)

------------------------------------------------------------------------
-- Part 4.  Lemma 4:  Beta1 subset Par subset Beta
------------------------------------------------------------------------

beta1-Par : {n : Nat} {M N : Expr n} -> Beta1 M N -> Par M N
beta1-Par (beta {M = M} {N = N}) = par-beta (par-refl M) (par-refl N)
beta1-Par (beta-Pi1  {B = B} s)  = par-Pi  (beta1-Par s) (par-refl B)
beta1-Par (beta-Pi2  {A = A} s)  = par-Pi  (par-refl A)  (beta1-Par s)
beta1-Par (beta-Lam1 {M = M} s)  = par-Lam (beta1-Par s) (par-refl M)
beta1-Par (beta-Lam2 {A = A} s)  = par-Lam (par-refl A)  (beta1-Par s)
beta1-Par (beta-App1 {N = N} s)  = par-App (beta1-Par s) (par-refl N)
beta1-Par (beta-App2 {M = M} s)  = par-App (par-refl M)  (beta1-Par s)

Par-Beta : {n : Nat} {M N : Expr n} -> Par M N -> Beta M N
Par-Beta par-var        = beta-refl
Par-Beta par-U          = beta-refl
Par-Beta (par-Pi p q)   = Beta-Pi  (Par-Beta p) (Par-Beta q)
Par-Beta (par-Lam p q)  = Beta-Lam (Par-Beta p) (Par-Beta q)
Par-Beta (par-App p q)  = Beta-App (Par-Beta p) (Par-Beta q)
Par-Beta (par-beta p q) =
  Beta-trans (Beta-App (Beta-Lam2 (Par-Beta p)) (Par-Beta q)) (Beta-one beta)

------------------------------------------------------------------------
-- Part 5.  Lemma 5:  Par is closed under substitution
------------------------------------------------------------------------

Par-ren : {n m : Nat} (r : Ren n m) {M M' : Expr n} ->
  Par M M' -> Par (renExpr r M) (renExpr r M')
Par-ren r par-var       = par-var
Par-ren r par-U         = par-U
Par-ren r (par-Pi p q)  = par-Pi  (Par-ren r p) (Par-ren (liftRen r) q)
Par-ren r (par-Lam p q) = par-Lam (Par-ren r p) (Par-ren (liftRen r) q)
Par-ren r (par-App p q) = par-App (Par-ren r p) (Par-ren r q)
Par-ren r (par-beta {M' = M'} {N' = N'} p q) =
  Eq-transport (\ X -> Par _ X) (Eq-sym (ren-subst1 r M' N'))
    (par-beta (Par-ren (liftRen r) p) (Par-ren r q))

-- Two substitutions related pointwise by Par.
ParSub : {h g : Nat} -> Sub h g -> Sub h g -> Set
ParSub {g = g} sigma tau = (i : Fin g) -> Par (sigma i) (tau i)

liftSub-ParSub : {h g : Nat} (sigma tau : Sub h g) ->
  ParSub sigma tau -> ParSub (liftSub sigma) (liftSub tau)
liftSub-ParSub sigma tau ps fzero    = par-var
liftSub-ParSub sigma tau ps (fsuc i) = Par-ren wkRen (ps i)

Par-subst : {h g : Nat} (sigma tau : Sub h g) -> ParSub sigma tau ->
  {M M' : Expr g} -> Par M M' -> Par (substExpr sigma M) (substExpr tau M')
Par-subst sigma tau ps (par-var {i = i}) = ps i
Par-subst sigma tau ps par-U             = par-U
Par-subst sigma tau ps (par-Pi p q)      =
  par-Pi (Par-subst sigma tau ps p)
    (Par-subst (liftSub sigma) (liftSub tau) (liftSub-ParSub sigma tau ps) q)
Par-subst sigma tau ps (par-Lam p q)     =
  par-Lam (Par-subst sigma tau ps p)
    (Par-subst (liftSub sigma) (liftSub tau) (liftSub-ParSub sigma tau ps) q)
Par-subst sigma tau ps (par-App p q)     =
  par-App (Par-subst sigma tau ps p) (Par-subst sigma tau ps q)
Par-subst sigma tau ps (par-beta {M' = M'} {N' = N'} p q) =
  Eq-transport (\ X -> Par _ X) (subst-subst1-comm tau M' N')
    (par-beta
      (Par-subst (liftSub sigma) (liftSub tau) (liftSub-ParSub sigma tau ps) p)
      (Par-subst sigma tau ps q))

-- Lemma 5 in the form used by Lemma 7.
Par-subst1 : {n : Nat} {M M' : Expr (suc n)} {N N' : Expr n} ->
  Par M M' -> Par N N' -> Par (subst1 M N) (subst1 M' N')
Par-subst1 {N = N} {N' = N'} p q =
  Par-subst (subst1Sub N) (subst1Sub N') ext p
  where
    ext : ParSub (subst1Sub N) (subst1Sub N')
    ext fzero    = q
    ext (fsuc i) = par-var

------------------------------------------------------------------------
-- Part 6.  Lemma 7:  the diamond property for Par
--
-- The paper's Lemma 6 (inversion of >= 1) is not needed: it is the
-- nested pattern match in the two mixed cases below.
--
-- `Sigma` is a record with eta, so the results of the recursive calls
-- are taken apart by irrefutable `let` patterns rather than by `with`.
------------------------------------------------------------------------

-- `Common M N` = there is a term to which both M and N parallel reduce.
Common : {n : Nat} -> Expr n -> Expr n -> Set
Common {n} M N = Sigma (Expr n) (\ Z -> Pair (Par M Z) (Par N Z))

Par-diamond : {n : Nat} {M1 M2 M3 : Expr n} ->
  Par M1 M2 -> Par M1 M3 -> Common M2 M3

-- case 1 of the paper: an axiom.
Par-diamond {M2 = M2} par-var par-var = mkSigma M2 (mkSigma par-var par-var)
Par-diamond {M2 = M2} par-U   par-U   = mkSigma M2 (mkSigma par-U par-U)

-- cases 2 and 3 of the paper, merged: the congruence rules.
Par-diamond (par-Pi p q) (par-Pi p' q') =
  let mkSigma A4 (mkSigma a1 a2) = Par-diamond p p'
      mkSigma B4 (mkSigma b1 b2) = Par-diamond q q'
  in mkSigma (Pi A4 B4) (mkSigma (par-Pi a1 b1) (par-Pi a2 b2))
Par-diamond (par-Lam p q) (par-Lam p' q') =
  let mkSigma A4 (mkSigma a1 a2) = Par-diamond p p'
      mkSigma M4 (mkSigma m1 m2) = Par-diamond q q'
  in mkSigma (Lam A4 M4) (mkSigma (par-Lam a1 m1) (par-Lam a2 m2))

-- case 5.1 of the paper.
Par-diamond (par-App p q) (par-App p' q') =
  let mkSigma M4 (mkSigma m1 m2) = Par-diamond p p'
      mkSigma N4 (mkSigma n1 n2) = Par-diamond q q'
  in mkSigma (App M4 N4) (mkSigma (par-App m1 n1) (par-App m2 n2))

-- case 5.2 of the paper: congruence against a contracted redex.
Par-diamond (par-App (par-Lam pA pM) pN) (par-beta qM qN) =
  let mkSigma M4 (mkSigma m1 m2) = Par-diamond pM qM
      mkSigma N4 (mkSigma n1 n2) = Par-diamond pN qN
  in mkSigma (subst1 M4 N4)
       (mkSigma (par-beta m1 n1) (Par-subst1 m2 n2))

-- subcase 4.1 of the paper: the mirror image of the previous case.
Par-diamond (par-beta pM pN) (par-App (par-Lam qA qM) qN) =
  let mkSigma M4 (mkSigma m1 m2) = Par-diamond pM qM
      mkSigma N4 (mkSigma n1 n2) = Par-diamond pN qN
  in mkSigma (subst1 M4 N4)
       (mkSigma (Par-subst1 m1 n1) (par-beta m2 n2))

-- subcase 4.2 of the paper: both sides contract the redex.
Par-diamond (par-beta pM pN) (par-beta qM qN) =
  let mkSigma M4 (mkSigma m1 m2) = Par-diamond pM qM
      mkSigma N4 (mkSigma n1 n2) = Par-diamond pN qN
  in mkSigma (subst1 M4 N4)
       (mkSigma (Par-subst1 m1 n1) (Par-subst1 m2 n2))

------------------------------------------------------------------------
-- Part 7.  Lemma 8:  the diamond property lifts to the closure
--
-- This is "repeated use of lemma 7 (see figure 2, page 40)": the strip
-- lemma followed by an induction on the other reduction sequence.
------------------------------------------------------------------------

-- The reflexive transitive closure of Par.  By construction this is
-- the paper's Lemma 3.
data ParStar : {n : Nat} -> Expr n -> Expr n -> Set where
  ps-refl : {n : Nat} {M : Expr n} -> ParStar M M
  ps-step : {n : Nat} {M N P : Expr n} ->
            Par M N -> ParStar N P -> ParStar M P

ParStar-trans : {n : Nat} {M N P : Expr n} ->
  ParStar M N -> ParStar N P -> ParStar M P
ParStar-trans ps-refl        r2 = r2
ParStar-trans (ps-step p r1) r2 = ps-step p (ParStar-trans r1 r2)

CommonStar : {n : Nat} -> Expr n -> Expr n -> Set
CommonStar {n} M N = Sigma (Expr n) (\ Z -> Pair (ParStar M Z) (ParStar N Z))

Strip : {n : Nat} -> Expr n -> Expr n -> Set
Strip {n} M N = Sigma (Expr n) (\ Z -> Pair (ParStar M Z) (Par N Z))

-- The strip lemma: one Par step against a whole ParStar sequence.
Par-strip : {n : Nat} {M1 M2 M3 : Expr n} ->
  Par M1 M2 -> ParStar M1 M3 -> Strip M2 M3
Par-strip {M2 = M2} p ps-refl = mkSigma M2 (mkSigma ps-refl p)
Par-strip p (ps-step q qs) =
  let mkSigma Z (mkSigma pz qz) = Par-diamond p q
      mkSigma W (mkSigma zw mw) = Par-strip qz qs
  in mkSigma W (mkSigma (ps-step pz zw) mw)

ParStar-diamond : {n : Nat} {M1 M2 M3 : Expr n} ->
  ParStar M1 M2 -> ParStar M1 M3 -> CommonStar M2 M3
ParStar-diamond {M3 = M3} ps-refl qs = mkSigma M3 (mkSigma qs ps-refl)
ParStar-diamond (ps-step p ps) qs =
  let mkSigma Z (mkSigma pz qz) = Par-strip p qs
      mkSigma W (mkSigma zw mw) = ParStar-diamond ps pz
  in mkSigma W (mkSigma zw (ps-step qz mw))

------------------------------------------------------------------------
-- Part 8.  Beta and ParStar have the same closure  (Lemma 4 again)
------------------------------------------------------------------------

Beta-ParStar : {n : Nat} {M N : Expr n} -> Beta M N -> ParStar M N
Beta-ParStar beta-refl       = ps-refl
Beta-ParStar (beta-step s r) = ps-step (beta1-Par s) (Beta-ParStar r)

ParStar-Beta : {n : Nat} {M N : Expr n} -> ParStar M N -> Beta M N
ParStar-Beta ps-refl       = beta-refl
ParStar-Beta (ps-step p r) = Beta-trans (Par-Beta p) (ParStar-Beta r)

------------------------------------------------------------------------
-- Part 9.  Lemma 8 for Beta:  confluence
------------------------------------------------------------------------

CommonBeta : {n : Nat} -> Expr n -> Expr n -> Set
CommonBeta {n} M N = Sigma (Expr n) (\ Z -> Pair (Beta M Z) (Beta N Z))

Beta-confluent : {n : Nat} {M1 M2 M3 : Expr n} ->
  Beta M1 M2 -> Beta M1 M3 -> CommonBeta M2 M3
Beta-confluent r1 r2 =
  let mkSigma Z (mkSigma z1 z2) =
        ParStar-diamond (Beta-ParStar r1) (Beta-ParStar r2)
  in mkSigma Z (mkSigma (ParStar-Beta z1) (ParStar-Beta z2))

------------------------------------------------------------------------
-- Part 10.  Lemma 9 and Theorem 10:  the Church-Rosser theorem
------------------------------------------------------------------------

Conv-common : {n : Nat} {M N : Expr n} -> Conv M N -> CommonBeta M N
Conv-common (conv-beta {M = M} {N = N}) =
  mkSigma (subst1 M N) (mkSigma (Beta-one beta) beta-refl)
Conv-common (conv-refl {M = M}) = mkSigma M (mkSigma beta-refl beta-refl)
Conv-common (conv-sym c) =
  let mkSigma Z (mkSigma z1 z2) = Conv-common c
  in mkSigma Z (mkSigma z2 z1)
-- the case of transitivity of = is the one that uses Lemma 8.
Conv-common (conv-trans c1 c2) =
  let mkSigma Z1 (mkSigma m1 n1) = Conv-common c1
      mkSigma Z2 (mkSigma n2 l2) = Conv-common c2
      mkSigma W  (mkSigma w1 w2) = Beta-confluent n1 n2
  in mkSigma W (mkSigma (Beta-trans m1 w1) (Beta-trans l2 w2))
Conv-common (conv-Pi c1 c2) =
  let mkSigma A4 (mkSigma a1 a2) = Conv-common c1
      mkSigma B4 (mkSigma b1 b2) = Conv-common c2
  in mkSigma (Pi A4 B4) (mkSigma (Beta-Pi a1 b1) (Beta-Pi a2 b2))
Conv-common (conv-Lam c1 c2) =
  let mkSigma A4 (mkSigma a1 a2) = Conv-common c1
      mkSigma M4 (mkSigma m1 m2) = Conv-common c2
  in mkSigma (Lam A4 M4) (mkSigma (Beta-Lam a1 m1) (Beta-Lam a2 m2))
Conv-common (conv-App c1 c2) =
  let mkSigma M4 (mkSigma m1 m2) = Conv-common c1
      mkSigma N4 (mkSigma n1 n2) = Conv-common c2
  in mkSigma (App M4 N4) (mkSigma (Beta-App m1 n1) (Beta-App m2 n2))

-- Theorem 10 (Church-Rosser).  If M = N then there is a term Z with
-- M >= Z and N >= Z.
church-rosser : {n : Nat} {M N : Expr n} -> Conv M N -> CommonBeta M N
church-rosser = Conv-common

------------------------------------------------------------------------
-- Part 11.  Beta conversion, and the fact that it is an equivalence
--
-- `Conv` above is the convertibility of the paper, generated
-- inductively; it is an equivalence relation because reflexivity,
-- symmetry and transitivity are among its constructors, so nothing is
-- proved by observing that.
--
-- Beta conversion proper is the *semantic* relation: M and N are
-- beta-convertible when they have a common reduct.  Reflexivity and
-- symmetry are immediate, but TRANSITIVITY is exactly the
-- Church-Rosser theorem -- given
--
--        M          N          P
--         \        / \        /
--          v      v   v      v
--           Z1            Z2
--
-- there is no reason for Z1 and Z2 to be comparable, and only
-- confluence applied at N produces the common reduct of Z1 and Z2 that
-- closes the diagram.  This is the sense in which, as the paper puts it
-- on p.128, "the Church-Rosser theorem is a kind of cut elimination
-- theorem, the transitivity of = in the lambda-calculus corresponding
-- to the cut".
------------------------------------------------------------------------

BConv : {n : Nat} -> Expr n -> Expr n -> Set
BConv M N = CommonBeta M N

BConv-red : {n : Nat} {M N : Expr n} -> Beta M N -> BConv M N
BConv-red {N = N} r = mkSigma N (mkSigma r beta-refl)

BConv-beta : {n : Nat} {A : Expr n} {M : Expr (suc n)} {N : Expr n} ->
  BConv (App (Lam A M) N) (subst1 M N)
BConv-beta = BConv-red (Beta-one beta)

------------------------------------------------------------------------
-- Equivalence.  Only transitivity uses the Church-Rosser theorem.
------------------------------------------------------------------------

BConv-refl : {n : Nat} {M : Expr n} -> BConv M M
BConv-refl {M = M} = mkSigma M (mkSigma beta-refl beta-refl)

BConv-sym : {n : Nat} {M N : Expr n} -> BConv M N -> BConv N M
BConv-sym c =
  let mkSigma Z (mkSigma z1 z2) = c
  in mkSigma Z (mkSigma z2 z1)

-- The whole point: `Beta-confluent` (the paper's Lemma 8) is what makes
-- beta conversion transitive.
BConv-trans : {n : Nat} {M N P : Expr n} -> BConv M N -> BConv N P -> BConv M P
BConv-trans c1 c2 =
  let mkSigma Z1 (mkSigma m1 n1) = c1
      mkSigma Z2 (mkSigma n2 p2) = c2
      mkSigma W  (mkSigma w1 w2) = Beta-confluent n1 n2
  in mkSigma W (mkSigma (Beta-trans m1 w1) (Beta-trans p2 w2))

------------------------------------------------------------------------
-- Beta conversion is a congruence
------------------------------------------------------------------------

BConv-Pi : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  BConv A A' -> BConv B B' -> BConv (Pi A B) (Pi A' B')
BConv-Pi c1 c2 =
  let mkSigma A4 (mkSigma a1 a2) = c1
      mkSigma B4 (mkSigma b1 b2) = c2
  in mkSigma (Pi A4 B4) (mkSigma (Beta-Pi a1 b1) (Beta-Pi a2 b2))

BConv-Lam : {n : Nat} {A A' : Expr n} {M M' : Expr (suc n)} ->
  BConv A A' -> BConv M M' -> BConv (Lam A M) (Lam A' M')
BConv-Lam c1 c2 =
  let mkSigma A4 (mkSigma a1 a2) = c1
      mkSigma M4 (mkSigma m1 m2) = c2
  in mkSigma (Lam A4 M4) (mkSigma (Beta-Lam a1 m1) (Beta-Lam a2 m2))

BConv-App : {n : Nat} {M M' N N' : Expr n} ->
  BConv M M' -> BConv N N' -> BConv (App M N) (App M' N')
BConv-App c1 c2 =
  let mkSigma M4 (mkSigma m1 m2) = c1
      mkSigma N4 (mkSigma n1 n2) = c2
  in mkSigma (App M4 N4) (mkSigma (Beta-App m1 n1) (Beta-App m2 n2))

------------------------------------------------------------------------
-- BConv is the convertibility of the paper
--
-- One direction is the Church-Rosser theorem itself; the other is
-- immediate.  So `BConv` really deserves the name "beta conversion",
-- and `Conv` -- which is an equivalence relation for free -- is closed
-- under nothing more than `BConv` is.
------------------------------------------------------------------------

Beta1-Conv : {n : Nat} {M N : Expr n} -> Beta1 M N -> Conv M N
Beta1-Conv beta            = conv-beta
Beta1-Conv (beta-Pi1  s)   = conv-Pi  (Beta1-Conv s) conv-refl
Beta1-Conv (beta-Pi2  s)   = conv-Pi  conv-refl (Beta1-Conv s)
Beta1-Conv (beta-Lam1 s)   = conv-Lam (Beta1-Conv s) conv-refl
Beta1-Conv (beta-Lam2 s)   = conv-Lam conv-refl (Beta1-Conv s)
Beta1-Conv (beta-App1 s)   = conv-App (Beta1-Conv s) conv-refl
Beta1-Conv (beta-App2 s)   = conv-App conv-refl (Beta1-Conv s)

Beta-Conv : {n : Nat} {M N : Expr n} -> Beta M N -> Conv M N
Beta-Conv beta-refl       = conv-refl
Beta-Conv (beta-step s r) = conv-trans (Beta1-Conv s) (Beta-Conv r)

Conv-BConv : {n : Nat} {M N : Expr n} -> Conv M N -> BConv M N
Conv-BConv = church-rosser

BConv-Conv : {n : Nat} {M N : Expr n} -> BConv M N -> Conv M N
BConv-Conv c =
  let mkSigma Z (mkSigma z1 z2) = c
  in conv-trans (Beta-Conv z1) (conv-sym (Beta-Conv z2))

------------------------------------------------------------------------
-- Part 12.  Normal forms, and their uniqueness
--
-- A term is in normal form when no beta step applies to it.  This is
-- the negative definition; it is all that is needed here, and it makes
-- `NF-Beta-refl` (a normal form reduces only to itself) immediate by
-- pattern matching.  A structural characterisation (an inductive
-- normal/neutral predicate) would have to be proved equivalent to it,
-- and buys nothing for uniqueness.
------------------------------------------------------------------------

Empty-elim : {A : Set} -> Empty -> A
Empty-elim ()

NF : {n : Nat} -> Expr n -> Set
NF {n} M = (N : Expr n) -> Beta1 M N -> Empty

-- A term in normal form reduces to itself only.
NF-Beta-refl : {n : Nat} {M Z : Expr n} -> NF M -> Beta M Z -> Eq M Z
NF-Beta-refl nf beta-refl                = refl
NF-Beta-refl nf (beta-step {N = N} s r)  = Empty-elim (nf N s)

-- Uniqueness of normal forms.  If M reduces to M1 and to M2 and both
-- are normal, then M1 and M2 are the SAME term.
--
--            M
--           / \
--          v   v
--        M1     M2       both normal
--           \ /
--            v
--            Z           confluence: M1 >= Z and M2 >= Z
--
-- and a normal form only reduces to itself, so M1 = Z = M2.
NF-unique : {n : Nat} {M M1 M2 : Expr n} ->
  Beta M M1 -> Beta M M2 -> NF M1 -> NF M2 -> Eq M1 M2
NF-unique r1 r2 nf1 nf2 =
  let mkSigma Z (mkSigma z1 z2) = Beta-confluent r1 r2
  in Eq-trans (NF-Beta-refl nf1 z1) (Eq-sym (NF-Beta-refl nf2 z2))

-- The same statement for beta conversion rather than for a common
-- ancestor: convertible normal forms are equal.  Note this is strictly
-- more general -- take the conversion given by the two reductions.
NF-unique-BConv : {n : Nat} {M1 M2 : Expr n} ->
  BConv M1 M2 -> NF M1 -> NF M2 -> Eq M1 M2
NF-unique-BConv c nf1 nf2 =
  let mkSigma Z (mkSigma z1 z2) = c
  in Eq-trans (NF-Beta-refl nf1 z1) (Eq-sym (NF-Beta-refl nf2 z2))

-- ... and hence for the convertibility of the paper.
NF-unique-Conv : {n : Nat} {M1 M2 : Expr n} ->
  Conv M1 M2 -> NF M1 -> NF M2 -> Eq M1 M2
NF-unique-Conv c = NF-unique-BConv (church-rosser c)

------------------------------------------------------------------------
-- Part 13.  Injectivity of Pi for beta conversion
--
-- This is the application the whole theorem exists for.  `Conv` is
-- generated by rules that never take a product apart, so there is no
-- induction on a `Conv` derivation that yields injectivity: the
-- transitivity rule destroys the shape of the middle term.  Confluence
-- replaces that induction, because reduction DOES preserve the shape:
-- every reduct of a product is a product, and its two components are
-- reducts of the two components.
--
-- Note this is injectivity for beta conversion of RAW terms.  It is not
-- the same statement as injectivity for the typed conversion judgement
-- of the rules of Type : Type, which also has eta.
------------------------------------------------------------------------

-- Constructor injectivity for Pi, at the level of Eq.
Pi-Eq-inv : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  Eq (Pi A B) (Pi A' B') -> Pair (Eq A A') (Eq B B')
Pi-Eq-inv refl = mkSigma refl refl

-- Every reduct of a product is a product, componentwise.
PiReduct : {n : Nat} -> Expr n -> Expr (suc n) -> Expr n -> Set
PiReduct {n} A B Z =
  Sigma (Expr n) (\ A2 ->
  Sigma (Expr (suc n)) (\ B2 ->
    Pair (Eq Z (Pi A2 B2)) (Pair (Beta A A2) (Beta B B2))))

-- The shape lemma.  The cases for beta, beta-Lam1/2 and beta-App1/2 are
-- absent because unification rules them out: none of them has a Pi as
-- its source.
Beta-Pi-inv : {n : Nat} {A : Expr n} {B : Expr (suc n)} {Z : Expr n} ->
  Beta (Pi A B) Z -> PiReduct A B Z
Beta-Pi-inv {A = A} {B = B} beta-refl =
  mkSigma A (mkSigma B (mkSigma refl (mkSigma beta-refl beta-refl)))
Beta-Pi-inv (beta-step (beta-Pi1 s) r) =
  let mkSigma A2 (mkSigma B2 (mkSigma e (mkSigma ra rb))) = Beta-Pi-inv r
  in mkSigma A2 (mkSigma B2 (mkSigma e (mkSigma (beta-step s ra) rb)))
Beta-Pi-inv (beta-step (beta-Pi2 s) r) =
  let mkSigma A2 (mkSigma B2 (mkSigma e (mkSigma ra rb))) = Beta-Pi-inv r
  in mkSigma A2 (mkSigma B2 (mkSigma e (mkSigma ra (beta-step s rb))))

-- Injectivity, in the sharp form: the components do not merely convert,
-- they have a COMMON REDUCT, produced by the theorem.
Pi-inj-BConv : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  Conv (Pi A B) (Pi A' B') -> Pair (BConv A A') (BConv B B')
Pi-inj-BConv {A' = A'} {B' = B'} c =
  let mkSigma Z (mkSigma z1 z2) = church-rosser c
      mkSigma A2 (mkSigma B2 (mkSigma e1 (mkSigma ra1 rb1))) = Beta-Pi-inv z1
      mkSigma A3 (mkSigma B3 (mkSigma e2 (mkSigma ra2 rb2))) = Beta-Pi-inv z2
      -- Pi A2 B2 = Z = Pi A3 B3, so the two decompositions agree
      mkSigma eA eB = Pi-Eq-inv (Eq-trans (Eq-sym e1) e2)
  in mkSigma
       (mkSigma A2 (mkSigma ra1 (Eq-transport (\ X -> Beta A' X) (Eq-sym eA) ra2)))
       (mkSigma B2 (mkSigma rb1 (Eq-transport (\ X -> Beta B' X) (Eq-sym eB) rb2)))

Pi-inj : {n : Nat} {A A' : Expr n} {B B' : Expr (suc n)} ->
  Conv (Pi A B) (Pi A' B') -> Pair (Conv A A') (Conv B B')
Pi-inj c =
  let mkSigma cA cB = Pi-inj-BConv c
  in mkSigma (BConv-Conv cA) (BConv-Conv cB)

------------------------------------------------------------------------
-- The companion "no confusion" statement, by the same argument: a
-- universe is never convertible to a product.  `U` is normal, so its
-- only reduct is itself, while every reduct of a product is a product.
------------------------------------------------------------------------

NF-U : {n : Nat} -> NF {n} U
NF-U _ ()

U-not-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} -> Eq (U {n}) (Pi A B) -> Empty
U-not-Pi ()

Conv-U-Pi : {n : Nat} {A : Expr n} {B : Expr (suc n)} ->
  Conv (U {n}) (Pi A B) -> Empty
Conv-U-Pi c =
  let mkSigma Z (mkSigma z1 z2) = church-rosser c
      mkSigma A2 (mkSigma B2 (mkSigma e _)) = Beta-Pi-inv z2
  in U-not-Pi (Eq-trans (NF-Beta-refl NF-U z1) e)
