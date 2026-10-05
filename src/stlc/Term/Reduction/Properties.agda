-- {-# OPTIONS --allow-unsolved-metas #-}

module Term.Reduction.Properties where

open import Prelude
open import Prelude.Reduction
open import Term
open import Term.Weakening renaming (lookup to lookupW)
open import Term.Substitution
open import Term.Substitution.Properties using (wk-sg; sub-sg)
open import Term.Reduction

private
  variable
    Γ Δ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ
    ρ : Wk Γ Δ

-- Closure of weah head reduction under weakening

wkW : (w : t ⟶w t') → wk ρ t ⟶w wk ρ t'
wkW {ρ = ρ} (β {t = t} {u = u}) =
  subst
    (app (abs (wk (keep ρ) t)) (wk ρ u) ⟶w_)
    (wk-sg {t = t})  -- wk (keep ρ) t) [ wk ρ u ]₀  ≡ wk ρ (t [ u ]₀)
    β
wkW (appl w) = appl (wkW w)

-- Closure of reduction under weakening

wkR : (r : t ⟶ t') → wk ρ t ⟶ wk ρ t'
wkR {ρ = ρ}  (β {t = t} {u = u}) =
  subst
    (app (abs (wk (keep ρ) t)) (wk ρ u) ⟶_)
    (wk-sg {t = t})  -- wk (keep ρ) t) [ wk ρ u ]₀  ≡ wk ρ (t [ u ]₀)
    β
wkR {ρ = ρ} (appl r) = appl (wkR r)
wkR {ρ = ρ} (appr r) = appr (wkR r)
wkR {ρ = ρ} (abs r) = abs (wkR r)

-- Closure of weak head reduction under substitution

subW : (w : t ⟶w t') → sub σ t ⟶w sub σ t'
-- subW β = subst (_ ⟶w_) (sym sub-sg) β -- not enough information
subW {σ = σ} (β {t = t} {u = u}) =
  subst
    (app (abs (sub (lift σ) t)) (sub σ u) ⟶w_)
    (sym (sub-sg {σ = σ} {t = t} {u = u}))
    β
subW (appl w) = appl (subW w)

-- Closure of reduction under substitution

subR1 : (r : t ⟶ t') → sub σ t ⟶ sub σ t'
subR1 {σ = σ} (β {t = t} {u = u}) =
  subst
    (app (abs (sub (lift σ) t)) (sub σ u) ⟶_)
    (sym (sub-sg {σ = σ} {t = t} {u = u}))
    β
subR1 (appl r) = appl (subR1 r)
subR1 (appr r) = appr (subR1 r)
subR1 (abs r) = abs (subR1 r)

-- Closure properties of mult-step reduction

wkR* : (rs : t ⟶* t') → wk ρ t ⟶* wk ρ t'
wkR* [] = []
wkR* (r ∷ rs) = wkR r ∷ wkR* rs

subR* :  (rs : t ⟶* t') → sub σ t ⟶* sub σ t'
subR* [] = []
subR* (r ∷ rs) = subR1 r ∷ subR* rs

absR* : t ⟶* t' → abs t ⟶* abs t'
absR* [] = []
absR* (r ∷ rs) = abs r ∷ absR* rs

applR* : t ⟶* t' → app t u ⟶* app t' u
applR* [] = []
applR* (r ∷ rs) = appl r ∷ applR* rs

apprR* : u ⟶* u' → app t u ⟶* app t u'
apprR* [] = []
apprR* (r ∷ rs) = appr r ∷ apprR* rs

appR* : t ⟶* t' → u ⟶* u' → app t u ⟶* app t' u'
appR* ts us = applR* ts Star.◅◅ apprR* us

-- Closure under substitution reduction: lemmata

lookup*S : (σs : σ ⟶*S σ') → lookup σ x ⟶* lookup σ' x
lookup*S {x = zero}  (σs ∙ rs) = rs
lookup*S {x = suc x} (σs ∙ rs) = lookup*S σs

reflS* : σ ⟶*S σ
reflS* {σ = ε} = ε
reflS* {σ = σ ∙ t} = reflS* ∙ []

compWS* : (σs : σ ⟶*S σ') → compWS ρ σ ⟶*S compWS ρ σ'
compWS* {ρ = ρ} ε = ε
compWS* {ρ = ρ} (σs ∙ rs) = compWS* σs ∙ wkR* rs

weakS* : (σs : σ ⟶*S σ') → weak {a = a} σ ⟶*S weak σ'
weakS* σs = compWS* {ρ = skip1} σs

liftS* : (σs : σ ⟶*S σ') → lift {a = a} σ ⟶*S lift σ'
liftS* σs = weakS* σs ∙ []

sub*S : (σs : σ ⟶*S σ') → sub σ t ⟶* sub σ' t
sub*S {t = var x}   σs = lookup*S σs
sub*S {t = abs t}   σs = absR* (sub*S {t = t} (liftS* σs))
sub*S {t = app t u} σs = appR* (sub*S {t = t} σs) (sub*S {t = u} σs)

-- Closure under substitution reduction: theorem

subR1S :  (r : t ⟶ t') (σs : σ ⟶*S σ') → sub σ t ⟶* sub σ' t'
subR1S {t' = t'} r σs = subR1 r ∷ sub*S {t = t'} σs

subR*S :  (rs : t ⟶* t') (σs : σ ⟶*S σ') → sub σ t ⟶* sub σ' t'
subR*S {t' = t'} rs σs = subR* rs Star.◅◅ sub*S {t = t'} σs

-- Closure of multi-step weak head reduction

applW* : t ⟶w* t' → app t u ⟶w* app t' u
applW* [] = []
applW* (r ∷ rs) = appl r ∷ applW* rs
