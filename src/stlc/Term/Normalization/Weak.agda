-- Weak β normalization
--
-- Goal: each well-typed term β-reduces to a weak normal form

module Term.Normalization.Weak where

open import Prelude
open import Prelude.Reduction
open import Term
open import Term.Weakening renaming (lookup to lookupR)
-- open import Term.Substitution
open import Term.Reduction
open import Term.Reduction.Properties
open import Term.Reduction.Standard
open import Term.NormalForm

private
  variable
    Γ Δ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    -- σ σ' : Sub Γ Δ
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

-- The inductive characterization is sound

mutual

  WNe→wne : WNe t → wne t
  WNe→wne var           =  wne-var
  WNe→wne (app wne wn)  =  wne-app (WNe→wne wne) (WN→wn wn)

  WN→wn : WN t → wn t
  WN→wn (ne wne)    =  wne→wn (WNe→wne wne)
  WN→wn (abs wn)    =  wn-abs (WN→wn wn)
  WN→wn (exp w wn)  =  whd-wn w (WN→wn wn)

-- For completeness, we need to define the closure of WNe under weak-head expansion

data WNe* (t : Term Γ a) : Set where
  wne* : {t' : Term Γ a} (wne : WNe t') (ws : t ⟶w* t') → WNe* t

-- record WNe* (t : Term Γ a) : Set where
--   constructor wne*
--   field
--     {ne-t} : Term Γ a
--     isWNe  : WNe ne-t
--     reds   : t ⟶w* ne-t

-- A normal form is trivially weakly normalizing, even inductively

mutual

  Ne→WNe : Ne t → WNe t
  Ne→WNe var = var
  Ne→WNe (app neu nf) = app (Ne→WNe neu) (Nf→WN nf)

  Nf→WN : Nf t → WN t
  Nf→WN (ne neu) = ne (Ne→WNe neu)
  Nf→WN (abs nf) = abs (Nf→WN nf)

-- WN is closed under expansion

-- WN is closed under multiple weak head expansions

whd*-WN : t ⟶w* t' → WN t' → WN t
whd*-WN []       wn = wn
whd*-WN (w ∷ ws) wn = exp w (whd*-WN ws wn)

-- WN is closed under expansion with standard reduction sequence

mutual

  expand-WNe : t ⟶s t' → WNe t' → WNe* t
  expand-WNe (w ∷ s) d with expand-WNe s d
  ... | wne* wne ws = wne* wne (w ∷ ws)
  expand-WNe var d = wne* d []
  expand-WNe (abs s) ()
  expand-WNe (app s s₁) (app wne wn) with expand-WNe s wne | expand-WN s₁ wn
  ... | wne* wne' ws | wn' = wne* (app wne' wn') (applW* ws)

  expand-WN : t ⟶s t' → WN t' → WN t
  expand-WN (w ∷ s) wn = exp w (expand-WN s wn)
  expand-WN s (exp w wn) = expand-WN (snocSW s w) wn
  expand-WN s (ne wne) with expand-WNe s wne
  ... | wne* wne ws = whd*-WN ws (ne wne)
  expand-WN (abs s) (abs wn) = abs (expand-WN s wn)

-- The inductive characterization is complete

wne→WNe : wne t → WNe* t
wne→WNe (wneu neu rs) = expand-WNe rs (Ne→WNe neu)

wn→WN : wn t → WN t
wn→WN (wnorm nf rs) = expand-WN rs (Nf→WN nf)
