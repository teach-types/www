-- Weak β normalization
--
-- Goal: each well-typed term β-reduces to a weak normal form

module Term.Normalization.Weak where

open import Prelude
open import Prelude.Reduction
open import Term
open import Term.Weakening renaming (lookup to lookupR)
open import Term.Weakening.Properties    using (wk-id; wk-wk)
open import Term.Substitution
open import Term.Substitution.Properties using (sub-id; sub-S-sg; wk-sg)
open import Term.Reduction
open import Term.Reduction.Properties
open import Term.Reduction.Standard
open import Term.NormalForm

private
  variable
    Γ Δ Ξ : Context
    a b c : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ
    ρ : Wk Γ Δ

-- Weakly normalizing terms standard-reduce to a normal form.
-- For "wn t" we can also say "t has a normal form".

record wne (t : Term Γ a) : Set where
  constructor wneu
  field
    {nf} : Term Γ a
    neu  : Ne nf
    reds : t ⟶s nf

record wn (t : Term Γ a) : Set where
  constructor wnorm
  field
    {nf} : Term Γ a
    norm : Nf nf
    reds : t ⟶s nf

-- wn/wne have the same closure properties as normal forms.

wne-var : wne (var x)
wne-var = wneu var reflS

wne-app : wne t → wn u → wne (app t u)
wne-app (wneu neu rt) (wnorm nf ru) = wneu (app neu nf) (app rt ru)

wn-abs  : wn t → wn (abs t)
wn-abs (wnorm nf rs) = wnorm (abs nf) (abs rs)

wne→wn  : {t : Term Γ a} → wne t → wn t
wne→wn (wneu neu rs) = wnorm (ne neu) rs

-- Plus they are closed under expansion.

whd-wne : t ⟶w t' → wne t' → wne t
whd-wne w (wneu neu s) = wneu neu (w ∷ s)

whd-wn : t ⟶w t' → wn t' → wn t
whd-wn w (wnorm nf s) = wnorm nf (w ∷ s)

expand-wn : t ⟶s t' → wn t' → wn  t
expand-wn s (wnorm nf rs) = wnorm nf (transS s rs)

-- Inductive characterization of weakly normalizing terms:
-- The minimal predicate with the above closure properties.

mutual

  data WNe : Term Γ a → Set where
    var : WNe (var x)
    app : (wne : WNe t) (wn : WN u) → WNe (app t u)

  data WN : Term Γ a → Set where
    ne  : (wne : WNe t) → WN t
    abs : (wn : WN t) → WN (abs t)
    exp : (w : t ⟶w t') (wn : WN t') → WN t

-- Closure under weakening

mutual

  wk-WNe : (ρ : Wk Γ Δ) {t : Term Δ a} → WNe t → WNe (wk ρ t)
  wk-WNe ρ var = var
  wk-WNe ρ (app wne wn) = app (wk-WNe ρ wne) (wk-WN ρ wn)

  wk-WN : (ρ : Wk Γ Δ) {t : Term Δ a} → WN t → WN (wk ρ t)
  wk-WN ρ (ne wne) = ne (wk-WNe ρ wne)
  wk-WN ρ (abs wn) = abs (wk-WN (keep ρ) wn)
  wk-WN ρ (exp w wn) = exp (wkW w) (wk-WN ρ wn)

------------------------------------------------------------------------
-- Soundness of the inductive characterization

-- The inductive characterization is sound.
-- Proof by induction on WNe/WN, using the closure properties of wne/wn.

mutual

  WNe→wne : WNe t → wne t
  WNe→wne var           =  wne-var
  WNe→wne (app wne wn)  =  wne-app (WNe→wne wne) (WN→wn wn)

  WN→wn : WN t → wn t
  WN→wn (ne wne)    =  wne→wn (WNe→wne wne)
  WN→wn (abs wn)    =  wn-abs (WN→wn wn)
  WN→wn (exp w wn)  =  whd-wn w (WN→wn wn)

------------------------------------------------------------------------
-- Completeness of the inductive characterization

-- We first show that Ne/Nf is contained in WNe/WN,
-- then we show that the latter are closed under expansion
-- with standard reduction sequences.

-- For WNe, this is actually not true, so we define a relaxed WNe*
-- that is closed under weak-head expansion.

data WNe* (t : Term Γ a) : Set where
  wne* : {t' : Term Γ a} (wne : WNe t') (ws : t ⟶w* t') → WNe* t

-- record WNe* (t : Term Γ a) : Set where
--   constructor wne*
--   field
--     {ne-t} : Term Γ a
--     isWNe  : WNe ne-t
--     reds   : t ⟶w* ne-t

-- Step 1 of completeness:
-- A normal form is trivially weakly normalizing, even inductively

mutual

  Ne→WNe : Ne t → WNe t
  Ne→WNe var = var
  Ne→WNe (app neu nf) = app (Ne→WNe neu) (Nf→WN nf)

  Nf→WN : Nf t → WN t
  Nf→WN (ne neu) = ne (Ne→WNe neu)
  Nf→WN (abs nf) = abs (Nf→WN nf)

-- Step 2 of completeness:
-- WN is closed under expansion

-- WN is closed under multiple weak head expansions.
-- Trivial induction on the weak head expansion sequence.

whd*-WN : t ⟶w* t' → WN t' → WN t
whd*-WN []       wn = wn
whd*-WN (w ∷ ws) wn = exp w (whd*-WN ws wn)

-- WN is closed under expansion with standard reduction sequences.

mutual

  -- If  t ⟶s t'  and  WNe t'  then  WNe* t.
  -- By induction on t ⟶s t'.
  expand-WNe : t ⟶s t' → WNe t' → WNe* t
  expand-WNe (w ∷ s) d with expand-WNe s d
  ... | wne* wne ws = wne* wne (w ∷ ws)
  expand-WNe var d = wne* d []
  expand-WNe (abs s) ()
  expand-WNe (app s s₁) (app wne wn) with expand-WNe s wne | expand-WN s₁ wn
  ... | wne* wne' ws | wn' = wne* (app wne' wn') (applW* ws)

  -- If  t ⟶s t'  and  WN t'  then  WN t.
  -- By main induction on WN t' and side induction on t ⟶s t'.
  expand-WN : t ⟶s t' → WN t' → WN t
  expand-WN (w ∷ s) wn = exp w (expand-WN s wn)
  expand-WN s (exp w wn) = expand-WN (snocSW s w) wn
  expand-WN s (ne wne) with expand-WNe s wne
  ... | wne* wne ws = whd*-WN ws (ne wne)
  expand-WN (abs s) (abs wn) = abs (expand-WN s wn)

-- Putting steps 1 and 2 together gives our completeness theorem:
-- The inductive characterization is complete.

wne→WNe : wne t → WNe* t
wne→WNe (wneu neu rs) = expand-WNe rs (Ne→WNe neu)

wn→WN : wn t → WN t
wn→WN (wnorm nf rs) = expand-WN rs (Nf→WN nf)

------------------------------------------------------------------------
-- Strengthening weak normalization

-- We need that WN (app t x) implies WN t if x does not appear in t.

-- First, we prove that if a weakened term weak-head reduces,
-- so does its original form.

whd-strengthen : wk ρ t ⟶w t' → ∃ λ u → (t ⟶w u) × (wk ρ u ≡ t')
whd-strengthen {t = app (var x) u} (appl ())
whd-strengthen {t = app (abs t) u} β = t [ u ]₀ , β , ≡.sym (wk-sg {t = t})
  -- Need:  wk ρ (t [ u ]₀) ≡ wk (keep ρ) t [ wk ρ u ]₀
whd-strengthen {t = app (app t u₁) u₂} (appl r) with whd-strengthen r
... | _ , r' , refl = _ , appl r' , refl

-- We prove that weakened WN terms are still WN if you drop the weakening.

mutual
  WNe-strengthen : WNe (wk ρ t) → WNe t
  WNe-strengthen {t = var x} var = var
  WNe-strengthen {t = abs t} ()
  WNe-strengthen {t = app t u} (app wne wn) = app (WNe-strengthen wne) (WN-strengthen wn)

  WN-strengthen : WN (wk ρ t) → WN t
  WN-strengthen {t = abs t} (abs wn) = abs (WN-strengthen wn)
  WN-strengthen (ne wne) = ne (WNe-strengthen wne)
  WN-strengthen (exp w wn) with whd-strengthen w
  ... | _ , w' , refl = exp w' (WN-strengthen wn)

-- Lemma: if  WN (app (↑ t) x₀)  then  WN t.

WN-η-contract : ∀ {t : Term Γ (a ⇒ b)} → WN (app (wk (skip idW) t) (var zero)) → WN t
WN-η-contract (ne (app wne _)) = ne (WNe-strengthen wne)
WN-η-contract (exp w wn) = {!!}

------------------------------------------------------------------------
-- Normalization proof by reducibility.
--
-- We refine the Kripke-Model of our normalization-by-evaluation proof
-- by to the reducibility logical relation.
-- This way, we can prove that the normal form computed by the soundness
-- proof of the STLC is indeed a (standard) reduct of the original term.
--
-- The goal is:  if  Γ ⊢ t : a  then  t ⟶s t'  for some normal t'.
--
-- By soundness of WN this becomes:  if  Γ ⊢ t : a  then  WN t.
--
-- We cannot directly show that each well-typed term has a normal form,
-- since this property is not closed under application a priori.
--
-- A counterexample does not exist, since they are closed under application
-- a posteriori, but it exists in untyped lambda-calculus:
-- With δ = λ x → x x we have wn δ, but not wn (δ δ).
--
-- To get  WN t → WN u → WN (app t u)  we need to prove something
-- stronger about well-typed terms, namely that they are "reducible".
--
-- Reducibility:  Interpreting types as sets of weakly normalizing terms.
--
-- In the case of function types, we also require that terms behave
-- as "functions" meaning that they map reducible arguments to reducible results.
--
-- In that, we need to consider reducible arguments in a larger context
-- as we need to be able to apply a λ-term Term Γ (a ⇒ b)
-- to a new fresh variable a ∈ (Γ ∙ a) to show that it is weakly normalizing.
--
-- So, a term of base type is reducible if it is weakly normalizing.
-- A term t : Term Γ (a ⇒ b) of function type is reducible if for each
-- weakening ρ : Wk Δ Γ and each reducible argument u : Term Δ a
-- the application app (wk ρ t) u of the transported term t to u is reducible.

mutual
  Red : (Γ : Context) (a : Ty) (t : Term Γ a) → Set
  Red Γ (` α)   t = WN t
  Red Γ (a ⇒ b) t = ∀{Δ} (ρ : Wk Δ Γ) {u : Term Δ a} (⟦u⟧ : Red Δ a u) → Red Δ b (app (wk ρ t) u)

-- Reducibility for substitutions: a substitution is reducible if each of its terms is reducible.

data Reds Γ : (Δ : Context) (σ : Sub Γ Δ) → Set where
  ε  : Reds Γ ε ε
  _∙_ : (⟦σ⟧ : Reds Γ Δ σ) (⟦t⟧ : Red Γ a t) → Reds Γ (Δ ∙ a) (σ ∙ t)

-- Projecting a term from a reducible substitution.

⟦lookup⟧ : (⟦σ⟧ : Reds Γ Δ σ) (x : a ∈ Δ) → Red Γ a (lookup σ x)
⟦lookup⟧ (_ ∙ ⟦t⟧) zero    = ⟦t⟧
⟦lookup⟧ (⟦σ⟧ ∙ _) (suc x) = ⟦lookup⟧ ⟦σ⟧ x

-- Reducibility is closed under weak-head expansion.
-- Proof by induction on the type.

whd-Red : t ⟶w t' → Red Γ a t' → Red Γ a t
whd-Red {a = ` α}   w wn       = exp w wn
whd-Red {a = a ⇒ b} w ⟦t⟧ ρ ⟦u⟧ = whd-Red (appl (wkW w)) (⟦t⟧ ρ ⟦u⟧)

-- Reducibility is closed under weakening.
-- Proof by induction on the type.

wk-Red : Red Γ a t → Red Δ a (wk ρ t)
wk-Red {a = ` α}   {ρ = ρ}        wn = wk-WN ρ wn
wk-Red {a = a ⇒ b} {ρ = ρ} ⟦t⟧ ρ' ⟦u⟧ =
  subst
    (λ t → Red _ _ (app t _))
    (wk-wk)
    (⟦t⟧ (compWW ρ' ρ) ⟦u⟧)

-- Reducible substitutions are closed under weakening.
-- Proven pointwise.

wk-Reds : Reds Δ Γ σ → Reds Ξ Γ (compWS ρ σ)
wk-Reds ε = ε
wk-Reds (⟦σ⟧ ∙ ⟦t⟧) = wk-Reds ⟦σ⟧ ∙ wk-Red ⟦t⟧

-- Proving that each well-typed term is reducible still fails in the case of abs
-- where we need show that application to an arbitrary reducible argument
-- produces a reducible term after β-contraction.
-- Thus we need to be able to instantiate variables with reducible terms.

-- So we instead prove that each well-typed term is valid where
-- "validity" is reducibility under all reducible substitutions.

-- Valid terms ("semantic" terms).

Valid : {Γ : Context} {a : Ty} (t : Term Γ a) → Set
Valid {Γ = Γ} {a = a} t = ∀{Δ}{σ : Sub Δ Γ} (⟦σ⟧ : Reds Δ Γ σ) → Red Δ a (sub σ t)

-- Validity is closed under term constructors.

-- For variables it is just a projection from the reducible substitution.

valid-var : (x : a ∈ Γ) → Valid (var x)
valid-var x ⟦σ⟧ = ⟦lookup⟧ ⟦σ⟧ x

-- For abstractions, we need to work most: we need β-expansion
-- of reduciblity.

valid-abs : {t : Term (Γ ∙ a) b} → Valid t → Valid (abs t)
valid-abs {Γ = Γ} {a = a} {b = b} {t = t} ⟦t⟧ {σ = σ} ⟦σ⟧ ρ {u = u} ⟦u⟧ =
  whd-Red
    (subst
      (app (wk ρ (sub σ (abs t))) u ⟶w_)
      (sub-S-sg {ρ = ρ} {σ = σ} {t = t} {u = u})
      β)
    (⟦t⟧ {σ = compWS ρ σ ∙ u} (wk-Reds ⟦σ⟧ ∙ ⟦u⟧))

-- For application, validity holds by definition
-- (except for a cast with the identity renaming).

valid-app : Valid t → Valid u → Valid (app t u)
valid-app {t = t} {u = u} ⟦t⟧ ⟦u⟧ {σ = σ} ⟦σ⟧ =
  subst
    (λ t → Red _ _ (app t (sub σ u)))
    (wk-id {ρ = idW})
    (⟦t⟧ ⟦σ⟧ idW {u = sub σ u} (⟦u⟧ ⟦σ⟧))

-- Fundamental theorem: each well-typed term t is "valid".
-- By induction on t, all the work has been done already.

fund : (t : Term Γ a) → Valid t
fund (var x)   = valid-var x
fund (abs t)   = valid-abs {t = t} (fund t)
fund (app t u) = valid-app {t = t} {u = u} (fund t) (fund u)

-- To get from a valid term to a reducible term, we need to apply
-- it to a reducible substitution.
-- If we apply it to the identity substitution, the term will not change,
-- so we need to show that the identity substitution is reducible.

-- It is sufficient to show that variables are reducible.
-- But since we reason by induction on types,
-- we need to more generally show that each neutral term is reducible (wne→Red).
--
-- Simultaneously we show that each reducible term is weakly normalizing,
-- ("the escape lemma" Red→wn),
-- which we will also use in the final theorem.
-- This uses the fact that Red is closed under η-reduction.

mutual

  -- This is the equivalent to reflection.
  WNe→Red : {t : Term Γ a} → WNe t → Red Γ a t
  WNe→Red {a = ` α}   wne      = ne wne
  WNe→Red {a = a ⇒ b} ⟦t⟧ ρ ⟦u⟧ = WNe→Red (app (wk-WNe ρ ⟦t⟧) (Red→WN ⟦u⟧))

  -- This is the equivalent to reification.
  Red→WN : {t : Term Γ a} → Red Γ a t → WN t
  Red→WN {a =   ` α} wn = wn
  Red→WN {a = a ⇒ b} ⟦t⟧ = WN-η-contract (Red→WN (⟦t⟧ skip1 ⟦var0⟧))

  -- Reflection of the 0th variable.
  ⟦var0⟧ : Red (Γ ∙ a) a (var zero)
  ⟦var0⟧ {a = a} = WNe→Red var

-- The identity substitution is reducible.

⟦idS⟧ : Reds Γ Γ idS
⟦idS⟧ {Γ = ε}     = ε
⟦idS⟧ {Γ = Γ ∙ a} = wk-Reds ⟦idS⟧ ∙ ⟦var0⟧

-- Normalization theorem: each well-typed term t is weakly normalizing.
--
-- Proof steps:
-- * t is valid by the fundamental theorem.
-- * sub idS t is reducible by instantiation with the identity substitution.
-- * sub idS t is weakly normalizing.
-- * t is weakly normalizing.

normalization : (t : Term Γ a) → WN t
normalization t = subst WN (sub-id) (Red→WN (fund t ⟦idS⟧))

-- Q.E.D.




-- Not used: Reducible substitutions are closed under lifting.

⟦lift⟧ : (⟦σ⟧ : Reds Δ Γ σ) → Reds (Δ ∙ a) (Γ ∙ a) (lift σ)
⟦lift⟧ ⟦σ⟧ = wk-Reds ⟦σ⟧ ∙ ⟦var0⟧


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
