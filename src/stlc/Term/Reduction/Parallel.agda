-- Parallel reduction to show confluence of reduction

module Term.Reduction.Parallel where

open import Prelude
open import Prelude.Reduction
open import Term
open import Term.Weakening renaming (lookup to lookupR)
open import Term.Substitution
open import Term.Substitution.Properties using (sub-sg; wk-sg)
open import Term.Reduction
open import Term.Reduction.Properties

private
  variable
    Γ Δ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' t₁ t₂ t₃ : Term Γ a
    σ σ' : Sub Γ Δ
    ρ : Wk Γ Δ

-- Parallel reduction
-- "Contract as many /visible/ redexes as you like"

infix 1 _⟹_

data _⟹_ : (t t' : Term Γ a) → Set where
  β    :  (p : t ⟹ t') (q : u ⟹ u') → app (abs t) u ⟹ t' [ u' ]₀
  var  :  var x ⟹ var x
  abs  :  (p : t ⟹ t') → abs t ⟹ abs t'
  app  :  (p : t ⟹ t') (q : u ⟹ u') → app t u ⟹ app t' u'

-- Parallel reduction is reflexive (no redexes contracted)

reflP : t ⟹ t
reflP {t = var x}     =  var
reflP {t = abs t}     =  abs reflP
reflP {t = app t t₁}  =  app reflP reflP

-- Parallel reduction is closed under weakening

wkP : (p : t ⟹ t') → wk ρ t ⟹ wk ρ t'
wkP {ρ = ρ} (β {t = t} {t' = t'} {u = u} {u' = u'} p p₁) =
  subst
    (app (abs (wk (keep ρ) t)) (wk ρ u) ⟹_)
    (wk-sg {t = t'})  -- wk (keep ρ) t) [ wk ρ u ]₀  ≡ wk ρ (t [ u ]₀)
    ( β (wkP p) (wkP p₁))
wkP var         =  var
wkP (abs p)     =  abs (wkP p)
wkP (app p p₁)  =  app (wkP p) (wkP p₁)

-- Parallel reduction of substitution

infix 1 _⟹S_

data _⟹S_ : (σ σ' : Sub Γ Δ) → Set where
  ε    :  _⟹S_ {Γ = Γ} ε ε
  _∙_  :  (P : σ ⟹S σ') (p : t ⟹ t') → σ ∙ t ⟹S σ' ∙ t'

-- Parallel reduction of substitution is reflexive

reflPS : σ ⟹S σ
reflPS {σ = ε}      =  ε
reflPS {σ = σ ∙ t}  =  reflPS ∙ reflP

-- Parallel reduction of substitution is closed under weakening

wkPS :  σ ⟹S σ' → compWS ρ σ ⟹S compWS ρ σ'
wkPS {ρ = ρ} ε        =  ε
wkPS {ρ = ρ} (P ∙ p)  =  wkPS P ∙ wkP p

weakP : σ ⟹S σ' → weak {a = a} σ ⟹S weak σ'
weakP P = wkPS P

liftP : σ ⟹S σ' → lift {a = a} σ ⟹S lift σ'
liftP P = weakP P ∙ reflP

-- Projecting one parallel reduction step from substitution reduction

lookupP : σ ⟹S σ' → lookup σ x ⟹ lookup σ' x
lookupP {x = zero}   (P ∙ p)   =  p
lookupP {x = suc x}  (P ∙ p)   =  lookupP P

-- Closure of parallel reduction under substitution

subP : t ⟹ t' → σ ⟹S σ' → sub σ t ⟹ sub σ' t'
subP {σ = σ} {σ' = σ'} (β {t = t} {t' = t'} {u = u} {u' = u'} p p₁) P =
  -- sub σ (app (abs t) u) ⟹ sub σ' (t' [ u' ]₀)
  subst
   (app (abs (sub (lift σ) t)) (sub σ u) ⟹_)
   (sym (sub-sg {σ = σ'} {t = t'} {u = u'}))
   (β (subP p (liftP P)) (subP p₁ P))
subP var P         =  lookupP P
subP (abs p) P     =  abs (subP p (liftP P))
subP (app p p₁) P  =  app (subP p P) (subP p₁ P)

-- Complete development: maximal parallel step

_ᵒ : (t : Term Γ a) → Term Γ a
app (abs t) u  ᵒ  =  t ᵒ [ u ᵒ ]₀
var x          ᵒ  =  var x
abs t          ᵒ  =  abs (t ᵒ)
app t u        ᵒ  =  app (t ᵒ) (u ᵒ)

-- Remark: any term reduces (in parallel) to its complete development.
-- This follows from the next lemma but can be proven directly as warm-up.

mutual
  compl : t ⟹ t ᵒ
  compl {t = var x}    =  var
  compl {t = abs t}    =  abs compl
  compl {t = app t u}  =  compl-app

  compl-app : app t u ⟹ (app t u)ᵒ
  compl-app {t = var x}     =  app var compl
  compl-app {t = abs t}     =  β compl compl
  compl-app {t = app t t₁}  =  app compl-app compl

-- Maximal extension of a parallel step
-- If  t ⟹ t'  then  t' ⟹ tᵒ.

mutual
  extend : t ⟹ t' → t' ⟹ t ᵒ
  extend (β P Q)    =  subP (extend P) (reflPS ∙ extend Q)
  extend var        =  var
  extend (abs P)    =  abs (extend P)
  extend (app P Q)  =  extend-app P Q

  extend-app : t ⟹ t' → u ⟹ u' → app t' u' ⟹ (app t u) ᵒ
  extend-app (β P P₁)    Q  =  app (subP (extend P) (reflPS ∙ extend P₁)) (extend Q)
  extend-app var         Q  =  app var (extend Q)
  extend-app (abs P)     Q  =  β (extend P) (extend Q)
  extend-app (app P P₁)  Q  =  app (extend-app P P₁) (extend Q)

-- Diamond lemma for parallel reduction

diamond⟹ : t ⟹ t₁ → t ⟹ t₂ → ∃ λ t₃ → (t₁ ⟹ t₃) × (t₂ ⟹ t₃)
diamond⟹ {t = t} P₁ P₂ = t ᵒ , extend P₁ , extend P₂

-- Embedding of one-step reduction

to⟹ : t ⟶ t' → t ⟹ t'
to⟹ β         =  β reflP reflP
to⟹ (appl r)  =  app (to⟹ r) reflP
to⟹ (appr r)  =  app reflP (to⟹ r)
to⟹ (abs r)   =  abs (to⟹ r)

-- Embedding into multi-step reduction

from⟹ : t ⟹ t' → t ⟶* t'
from⟹ (β Pt Pu)    =  β ∷ subR*S (from⟹ Pt) (reflS* ∙ from⟹ Pu)
from⟹ var          =  []
from⟹ (abs P)      =  absR* (from⟹ P)
from⟹ (app Pt Pu)  =  appR* (from⟹ Pt) (from⟹ Pu)

-- Theorem: Confluence of reduction

confluence : Confluent (_⟶_ {Γ = Γ} {a = a})
confluence = sandwich to⟹ from⟹ diamond⟹
