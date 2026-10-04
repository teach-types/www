-- Standardization theorem for beta-reduction

-- Following Ralph Loader, Notes on Simply-Typed Lambda-Calculus, Exercise 1.20
-- https://www.lfcs.inf.ed.ac.uk/reports/98/ECS-LFCS-98-381/ECS-LFCS-98-381.pdf

module Term.Reduction.Standard where

open import Prelude
open import Term
open import Term.Weakening renaming (lookup to lookupR)
open import Term.Substitution
open import Term.Reduction
open import Term.Reduction.Properties

private
  variable
    Γ Δ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ
    ρ : Wk Γ Δ

-- Standard reduction
-- "Weak-head reduce the root first, then recursively standard-reduce the subterms"

infix 1 _⟶s_

data _⟶s_ : (t t' : Term Γ a) → Set where
  _∷_   :  (w : t ⟶w t') (s : t' ⟶s t'') → t ⟶s t''
  var   :  var x ⟶s var x
  abs   :  (s : t ⟶s t') → abs t ⟶s abs t'
  app   :  (sl : t ⟶s t') (sr : u ⟶s u') → app t u ⟶s app t' u'

-- Standard reduction is reflexive

reflS : (t : Term Γ a) → t ⟶s t
reflS (var x)    =  var
reflS (abs t)    =  abs (reflS t)
reflS (app t u)  =  app (reflS t) (reflS u)

-- Standard reduction is closed under renaming

wkS : t ⟶s t' → wk ρ t ⟶s wk ρ t'
wkS {ρ = ρ} (w ∷ s)     =  wkW w ∷ wkS s
wkS {ρ = ρ} var         =  reflS _
wkS {ρ = ρ} (abs s)     =  abs (wkS s)
wkS {ρ = ρ} (app s s₁)  =  app (wkS s) (wkS s₁)

-- Parallel standard reduction of substitutions

infix 1 _⟶S_

data _⟶S_ : (σ σ' : Sub Γ Δ) → Set where
  ε    :  _⟶S_ {Γ = Γ} ε ε
  _∙_  :  (S : σ ⟶S σ') (s : t ⟶s t') → σ ∙ t ⟶S σ' ∙ t'

-- Standard reduction of substitutions is reflexive

reflSS : σ ⟶S σ
reflSS {σ = ε}      =  ε
reflSS {σ = σ ∙ t}  =  reflSS ∙ reflS t

idSS : (idS {Γ = Γ}) ⟶S idS
idSS = reflSS

-- Projecting out one standard reduction

lookupS : (S : σ ⟶S σ') → lookup σ x ⟶s lookup σ' x
lookupS {x = zero}   (S ∙ s)   =  s
lookupS {x = suc x}  (S ∙ s)   =  lookupS S

-- Standard reduction of substitutions closed under weaking and lifting

weakS : (S : σ ⟶S σ') → weak {a = a} σ ⟶S weak σ'
weakS ε        =  ε
weakS (S ∙ s)  =  weakS S ∙ wkS s

liftS : (S : σ ⟶S σ') → lift {a = a} σ ⟶S lift σ'
liftS S = weakS S ∙ reflS _

-- Standard reduction is closed under standard-reduced substitutions

subS : (s : t ⟶s t') (S : σ ⟶S σ') → sub σ t ⟶s sub σ' t'
subS (w ∷ s)     S  =  subW w ∷ subS s S
subS  var        S  =  lookupS S
subS (abs s)     S  =  abs (subS s (liftS S))
subS (app s s₁)  S  =  app (subS s S) (subS s₁ S)

-- In particular under a single substitution

sub1S : (s : t ⟶s t') (s₁ : u ⟶s u') → t [ u ]₀ ⟶s t' [ u' ]₀
sub1S s s₁ = subS s (reflSS ∙ s₁)

-- If  t ⟶s t'  and  u ⟶s u'  then  (λt)u ⟶s t'[u'].

snocWh : (s : t ⟶s abs t') (s₁ : u ⟶s u') → app t u ⟶s t' [ u' ]₀
snocWh (w ∷ s)  s₁  =  appl w ∷ snocWh s s₁
snocWh (abs s)  s₁  =  β ∷ sub1S s s₁

-- Appending a reduction step at the end of a standard sequence

snocS : (s : t ⟶s t') (r : t' ⟶ t'') → t ⟶s t''
snocS (w ∷ s)     r         =  w ∷ snocS s r
snocS (abs s)     (abs r)   =  abs (snocS s r)
snocS (app s s₁)  β         =  snocWh s s₁
snocS (app s s₁)  (appl r)  =  app (snocS s r) s₁
snocS (app s s₁)  (appr r)  =  app s (snocS s₁ r)

-- Turning a reduction sequence into a standard sequence, beginning to end

standardizeˢ : t ⟶*ˢ t' → t ⟶s t'
standardizeˢ []        =  reflS _
standardizeˢ (rs ▷ r)  =  snocS (standardizeˢ rs) r

-- Standardization theorem

standardize : t ⟶* t' → t ⟶s t'
standardize = standardizeˢ ∘ reverse*
