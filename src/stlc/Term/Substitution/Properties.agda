-- {-# OPTIONS --allow-unsolved-metas #-}

-- Properties of substitutions and their operations.
-- This includes the category laws, but also laws of composing substitutions with weakenings,
-- extending and lifting substitutions.
--
-- We have 4 composition operations (compWW, compWS, compSS, compSW)
-- yielding 8 associativity lemmata (assocWWW...assocSSS).
-- Each of the composition operations also has an interpretation as composition of functions.
--
--     sub (compWS ρ σ)  = wk ρ ∘ sub σ
--     sub (compSS σ σ') = sub σ ∘ sub σ'
--     sub (compSW σ ρ)  = sub σ ∘ wk ρ
--
-- We also get laws for fromWk:
--
--     sub (fromWk ρ) = ren ρ
--
--     compWS ρ (fromWk ρ')          = fromWk (compWW ρ ρ')
--     compSW (fromWk ρ) ρ'          = fromWk (compWW ρ ρ')
--     compSS (fromWk ρ) (fromWk ρ') = fromWk (compWW ρ ρ')
--
-- There are further laws about the interaction of substitution extension
-- and weakening, such as:
--
--     compSS (σ ∙ t) (weak σ') ≡ compSS σ σ'
--
-- Only a few of the laws are used in the theory of equality reduction,
-- one is the distribution of a substitution over a single substitution.
--
--     sub-sg : sub σ (t [ u ]₀) ≡ (sub (lift σ) t) [ sub σ u ]₀
--
-- This one is used to prove that reduction is closed under substitution.
--
-- There is a similar lemma for distributing a weakening over a single substitution,
-- used to prove that reduction is closed under weakening.
--
--     sym wk-sg : wk ρ (t [ u ]₀) ≡ (wk (keep ρ) t) [ wk ρ u ]₀
--
-- Disclaimer:
-- For now, this module is not in perfect order.
-- Because of dependencies between lemmata, we cannot arrange them
-- in the most logical fashion (e.g. first all the category laws,
-- then more specific laws about substitution extension and lifting, etc.).
-- (But probably they could be arranged in a better way than now.)

module Term.Substitution.Properties where

open import Prelude
open import Term
open import Term.Weakening using (Wk; done; keep; skip; idW; skip1; wk; wk1; compWW) renaming (lookup to lookupW)
open import Term.Weakening.Properties
open import Term.Substitution

open ≡-Reasoning

private
  variable
    Γ Δ Φ : Context
    a : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' σ₁ σ₂ σ₃ : Sub Γ Δ
    ρ ρ' : Wk Γ Δ

-- (ρ ∘ σ) x = ρ(σ(x))

lookup-compWS : lookup (compWS ρ σ) x ≡ wk ρ (lookup σ x)
lookup-compWS {σ = σ ∙ t} {x = zero}  = refl
lookup-compWS {σ = σ ∙ t} {x = suc x} = lookup-compWS {σ = σ}

mutual

  -- ⌜ρ⌝(x) = var(ρ(x))

  lookup-fromWk : lookup (fromWk ρ) x ≡ var (lookupW ρ x)
  lookup-fromWk {ρ = keep ρ} {x = zero}  = refl
  lookup-fromWk {ρ = keep ρ} {x = suc x} = lookup-fromWk-lemma {ρ = ρ} {x = x}
  lookup-fromWk {ρ = skip ρ} {x = x}     = lookup-fromWk-lemma {ρ = ρ} {x = x}

  lookup-fromWk-lemma : lookup (weak {a = a} (fromWk ρ)) x ≡ var (suc (lookupW ρ x))
  lookup-fromWk-lemma {ρ = ρ} {x = x} =
    lookup (weak (fromWk ρ)) x           ≡⟨⟩
    lookup (compWS skip1 (fromWk ρ)) x   ≡⟨ lookup-compWS {σ = fromWk ρ} {x = x} ⟩
    wk skip1 (lookup (fromWk ρ) x)       ≡⟨ cong (wk skip1) (lookup-fromWk {ρ = ρ} {x = x}) ⟩
    wk skip1 (var (lookupW ρ x))         ≡⟨ cong (var ∘ suc) lookup-idW ⟩
    var (suc (lookupW ρ x))              ∎

-- ⌜ρ⌝(t) = ρ(t)

sub-fromWk : sub (fromWk ρ) t ≡ wk ρ t
sub-fromWk {ρ = ρ} {t = var x}    = lookup-fromWk {ρ = ρ} {x = x}
sub-fromWk {ρ = ρ} {t = abs t}    = cong abs sub-fromWk
sub-fromWk {ρ = ρ} {t = app t t₁} = cong₂ app sub-fromWk sub-fromWk

-- ⌜ρ⌝ ∘ σ = ρ ∘ σ

comp-fromWk-S : compSS (fromWk ρ) σ ≡ compWS ρ σ
comp-fromWk-S {ρ = ρ} {σ = ε}    = refl
comp-fromWk-S {ρ = ρ} {σ = σ ∙ t} = cong₂ _∙_ comp-fromWk-S sub-fromWk

-- σ ∘ ε = σ

compSW-done : compSW σ done ≡ σ
compSW-done {σ = ε} = refl

-- (ρ ∘ σ) ∘ ρ' = ρ ∘ (σ ∘ ρ')

assocWSW : compSW (compWS ρ σ) ρ' ≡ compWS ρ (compSW σ ρ')
assocWSW {ρ = ρ} {σ = σ} {ρ' = done} =
  compSW (compWS ρ σ) done ≡⟨ compSW-done ⟩
  compWS ρ σ               ≡⟨ cong (compWS ρ) (sym compSW-done) ⟩
  compWS ρ (compSW σ done)  ∎
assocWSW {ρ = ρ} {σ = σ ∙ t} {ρ' = skip ρ'} = assocWSW {σ = σ}
assocWSW {ρ = ρ} {σ = σ ∙ t} {ρ' = keep ρ'} = cong (_∙ wk ρ t) (assocWSW {σ = σ})

-- σ(ρ(x)) = (σ ∘ ρ)(x)

sub-lookupW : lookup σ (lookupW ρ x) ≡ lookup (compSW σ ρ) x
sub-lookupW {σ = σ}     {ρ = done}   {x = ()}
sub-lookupW {σ = σ ∙ t} {ρ = skip ρ} {x = x}     = sub-lookupW {σ = σ}
sub-lookupW {σ = σ ∙ t} {ρ = keep ρ} {x = zero}  = refl
sub-lookupW {σ = σ ∙ t} {ρ = keep ρ} {x = suc x} = sub-lookupW {σ = σ}

-- σ(σ'(x)) = (σ ∘ σ')(x)

sub-lookup : sub σ (lookup σ' x) ≡ lookup (compSS σ σ') x
sub-lookup {σ' = σ' ∙ t} {x = zero} = refl
sub-lookup {σ' = σ' ∙ t} {x = suc x} = sub-lookup {σ' = σ'}
-- sub-lookup {σ = σ} {σ' = []} {x = ()}  -- impossible

-- sub (sg t₁) (wk skip1 t) ≡ t

weak-compSW : compSW (weak {a = a} σ) ρ ≡ weak (compSW σ ρ)
weak-compSW {σ = σ} = assocWSW {σ = σ}

lift-compSW : compSW (lift {a = a} σ) (keep ρ) ≡ lift (compSW σ ρ)
lift-compSW {σ = σ} = cong (_∙ var zero) (weak-compSW {σ = σ})

sub-wk : sub σ (wk ρ t) ≡ sub (compSW σ ρ) t
sub-wk {σ = σ} {t = var x}   = sub-lookupW {σ = σ} {x = x}
sub-wk {σ = σ} {t = abs t}   = cong abs (trans (sub-wk {t = t}) (cong (λ σ → sub σ t) (lift-compSW {σ = σ})))
sub-wk         {t = app t u} = cong₂ app (sub-wk {t = t}) (sub-wk {t = u})

assocSWS : compSS (compSW σ ρ) σ' ≡ compSS σ (compWS ρ σ')
assocSWS {σ = σ} {ρ = ρ} {σ' = ε}     = refl
assocSWS {σ = σ} {ρ = ρ} {σ' = σ' ∙ t} = cong₂ _∙_ assocSWS (sym (sub-wk {t = t}))

wk-lookup : wk ρ (lookup σ x) ≡ lookup (compWS ρ σ) x
wk-lookup {σ = σ ∙ t} {x = zero} = refl
wk-lookup {σ = σ ∙ t} {x = suc x} = wk-lookup {σ = σ} {x = x}

assocWWS : compWS (compWW ρ ρ') σ ≡ compWS ρ (compWS ρ' σ)
assocWWS {σ = ε} = refl
assocWWS {σ = σ ∙ t} = cong₂ _∙_ assocWWS (wk-wk {t = t})

weak-compWS : weak {a = a} (compWS ρ σ) ≡ compWS (keep ρ) (weak σ)
weak-compWS {ρ = ρ} {σ = σ} =
  compWS skip1 (compWS ρ σ)          ≡⟨ sym assocWWS ⟩
  compWS (compWW skip1 ρ) σ          ≡⟨ cong (λ ρ → compWS (skip ρ) σ) (trans (comp-id-W) (sym (comp-W-id {ρ = ρ}))) ⟩
  compWS (compWW (keep ρ) skip1) σ   ≡⟨ assocWWS ⟩
  compWS (keep ρ) (compWS skip1 σ)   ∎

lift-compWS : lift {a = a} (compWS ρ σ) ≡ compWS (keep ρ) (lift σ)
lift-compWS = cong (_∙ var zero) weak-compWS

wk-sub : wk ρ (sub σ t) ≡ sub (compWS ρ σ) t
wk-sub {ρ = ρ} {σ = σ} {t = var x} = wk-lookup {σ = σ} {x = x}
wk-sub {ρ = ρ} {σ = σ} {t = abs t} = cong abs (
  wk (keep ρ) (sub (lift σ) t)     ≡⟨ wk-sub {t = t}  ⟩
  sub (compWS (keep ρ) (lift σ)) t  ≡⟨ cong (λ σ → sub σ t) (sym (lift-compWS {σ = σ}))  ⟩
  sub (lift (compWS ρ σ)) t         ∎)
wk-sub {ρ = ρ} {σ = σ} {t = app t u} = cong₂ app (wk-sub {σ = σ} {t = t}) (wk-sub {t = u})

assocWSS : compSS (compWS ρ σ) σ' ≡ compWS ρ (compSS σ σ')
assocWSS {ρ = ρ} {σ = σ} {σ' = ε} = refl
assocWSS {ρ = ρ} {σ = σ} {σ' = σ' ∙ t} = cong₂ _∙_ (assocWSS {σ = σ}) (sym (wk-sub {t = t}))

comp-S-idW : {ρ : Wk Γ Γ} → compSW σ ρ ≡ σ
comp-S-idW {σ = ε}    {ρ = done}   = refl
comp-S-idW {σ = σ ∙ t} {ρ = skip ρ} = case Wk-cons ρ of λ()
comp-S-idW {σ = σ ∙ t} {ρ = keep ρ} = cong (_∙ t) comp-S-idW

compSS-weak : compSS (weak {a = a} σ) σ' ≡ weak (compSS σ σ')
compSS-weak {σ = σ} {σ' = ε} = refl
compSS-weak {σ = σ} {σ' = σ' ∙ t} = cong₂ _∙_
 (compSS (compWS (skip idW) σ) σ' ≡⟨ assocWSS ⟩
  compWS (skip idW) (compSS σ σ') ∎)
 (sym (wk-sub {t = t}))

weak-compSS : compSS (lift {a = a} σ) (weak σ') ≡ weak (compSS σ σ')
weak-compSS {σ = σ} {σ' = σ'} =
   compSS (lift σ) (weak σ')          ≡⟨⟩
   compSS (lift σ) (compWS skip1 σ')  ≡⟨ sym (assocSWS {σ = lift σ}) ⟩
   compSS (compSW (lift σ) skip1) σ'  ≡⟨ cong (λ σ → compSS σ σ') comp-S-idW ⟩
   compSS (compWS skip1 σ) σ'         ≡⟨ assocWSS ⟩
   compWS skip1 (compSS σ σ')         ≡⟨⟩
   weak (compSS σ σ') ∎

lift-compSS : compSS (lift {a = a} σ) (lift σ') ≡ lift (compSS σ σ')
lift-compSS {σ = σ} {σ' = σ'} = cong (_∙ var zero) weak-compSS

sub-ext-weak : sub (σ ∙ u) (wk1 t) ≡ sub σ t
sub-ext-weak {σ = σ} {u = u} {t = t} =
  sub (σ ∙ u) (wk1 t)           ≡⟨⟩
  sub (σ ∙ u) (wk skip1 t)     ≡⟨ sub-wk {σ = σ ∙ u} {ρ = skip1} {t = t} ⟩
  sub (compSW (σ ∙ u) skip1) t  ≡⟨ cong (λ σ → sub σ t) comp-S-idW ⟩
  sub σ t             ∎

comp-ext-weak : compSS (σ ∙ t) (weak σ') ≡ compSS σ σ'
comp-ext-weak {σ' = ε} = refl
comp-ext-weak {σ = σ} {σ' = σ' ∙ t} =  cong₂ _∙_ comp-ext-weak (sub-ext-weak {σ = σ} {t = t})

-- Identity substitution

lookupS-id : lookup idS x ≡ var x
lookupS-id {x = zero}  = refl
lookupS-id {x = suc x} =
  lookup (compWS skip1 idS) x  ≡⟨ lookup-compWS {σ = idS} {x = x} ⟩
  wk skip1 (lookup idS x)      ≡⟨ cong wk1 lookupS-id ⟩
  wk1 (var x)                  ≡⟨ cong (λ x → var (suc x)) lookup-idW ⟩
  var (suc x)                  ∎

sub-id : sub idS t ≡ t
sub-id {t = var x}   = lookupS-id
sub-id {t = abs t}   = cong abs sub-id
sub-id {t = app t u} = cong₂ app sub-id sub-id

comp-id-S : compSS idS σ ≡ σ
comp-id-S {σ = ε} = refl
comp-id-S {σ = σ ∙ t} = cong₂ _∙_ comp-id-S sub-id

comp-S-id : compSS σ idS ≡ σ
comp-S-id {σ = ε}    = refl
comp-S-id {σ = σ ∙ t} = cong (_∙ t) (trans comp-ext-weak comp-S-id)

-- Composition of substitutions (compSS)

-- Consequence of comp-ext-weak
comp-sg-weak : compSS (sg t) (weak σ) ≡ σ
comp-sg-weak {t = t} {σ = σ} =
 compSS (sg t) (weak σ)     ≡⟨⟩
 compSS (idS ∙ t) (weak σ)  ≡⟨ comp-ext-weak ⟩
 compSS idS σ               ≡⟨ comp-id-S ⟩
  σ ∎

comp-sg-lift : compSS (sg t) (lift σ) ≡ σ ∙ t
comp-sg-lift {t = t} = cong (_∙ t) comp-sg-weak

sub-comp : sub σ (sub σ' t) ≡ sub (compSS σ σ') t
sub-comp {σ' = σ'} {t = var x}   = sub-lookup {σ' = σ'}
sub-comp           {t = abs t}   = cong abs (trans (sub-comp {t = t}) (cong (λ σ → sub σ t) lift-compSS))
sub-comp           {t = app t u} = cong₂ app (sub-comp {t = t}) (sub-comp {t = u})

assocSSS : compSS (compSS σ₁ σ₂) σ₃ ≡ compSS σ₁ (compSS σ₂ σ₃)
assocSSS {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = ε} = refl
assocSSS {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃ ∙ t} = cong₂ _∙_ assocSSS (sym (sub-comp {t = t}))

-- Payload: a lemma we are actually using for β.

sub-sg : sub σ (t [ u ]₀) ≡ (sub (lift σ) t) [ sub σ u ]₀
sub-sg {σ = σ} {t = t} {u = u} =
  sub σ (t [ u ]₀)                         ≡⟨ sub-comp {σ = σ} {σ' = sg u} {t = t} ⟩
  sub (compSS σ (sg u)) t                  ≡⟨⟩
  sub (compSS σ idS ∙ sub σ u) t           ≡⟨ cong (λ □ → sub (□ ∙ sub σ u) t) comp-S-id ⟩
  sub (σ ∙ sub σ u) t                      ≡⟨ cong (λ □ → sub (□ ∙ sub σ u) t) (sym comp-sg-weak) ⟩
  sub (compSS (idS ∙ sub σ u) (lift σ)) t  ≡⟨⟩
  sub (compSS (sg (sub σ u)) (lift σ)) t   ≡⟨ sym (sub-comp {t = t}) ⟩
  (sub (lift σ) t) [ sub σ u ]₀  ∎

-- A more general lemma, in the other direction:

sub-S-sg :  (wk (keep ρ) (sub (lift σ) t) [ u ]₀) ≡ (sub (compWS ρ σ ∙ u) t)
sub-S-sg {ρ = ρ} {σ = σ} {t = t} {u = u} =
  (wk (keep ρ) (sub (lift σ) t) [ u ]₀)          ≡⟨⟩
  sub (sg u) (wk (keep ρ) (sub (lift σ) t))      ≡⟨ cong (sub (sg u)) (wk-sub {ρ = keep ρ} {σ = lift σ} {t = t}) ⟩
  sub (sg u) (sub (compWS (keep ρ) (lift σ)) t)  ≡⟨ cong (λ σ → sub (sg u) (sub σ t)) (sym lift-compWS) ⟩
  sub (sg u) (sub (lift (compWS ρ σ)) t)         ≡⟨ sub-comp {σ = sg u} {σ' = lift (compWS ρ σ)} {t = t} ⟩
  sub (compSS (sg u) (lift (compWS ρ σ))) t      ≡⟨ cong (λ σ → sub σ t) comp-sg-lift ⟩
  sub (compWS ρ σ ∙ u) t                         ∎

-- More on relationship to weakenings

comp-S-W-emp : (σ : Sub Δ Γ) (ρ : Wk Γ ε) → compSW σ ρ ≡ ε
comp-S-W-emp ε      done     = refl
comp-S-W-emp (σ ∙ t) (skip ρ) = comp-S-W-emp σ ρ

comp-idW-S : {ρ : Wk Γ Γ} → compWS ρ σ ≡ σ
comp-idW-S {σ = ε} {ρ = ρ} = refl
comp-idW-S {σ = σ ∙ t} {ρ = ρ} = cong₂ _∙_ comp-idW-S wk-id

-- fromWk is a functor from Wk to Sub

fromWk-empty : (ρ : Wk Γ ε) → fromWk ρ ≡ ε
fromWk-empty done = refl
fromWk-empty (skip ρ) rewrite fromWk-empty ρ = refl

fromWk-comp : fromWk (compWW ρ ρ') ≡ compSS (fromWk ρ) (fromWk ρ')
fromWk-comp {ρ = ρ} {ρ' = done}    = fromWk-empty (compWW ρ done)

fromWk-comp {ρ = skip ρ} {ρ' = skip ρ'} =
   weak (fromWk (compWW ρ (skip ρ')))                  ≡⟨ cong weak (fromWk-comp {ρ = ρ}) ⟩  -- IH
   weak (compSS (fromWk ρ) (fromWk (skip ρ')))         ≡⟨⟩
   weak (compSS (fromWk ρ) (weak (fromWk ρ')))         ≡⟨ sym compSS-weak ⟩
   compSS (weak (fromWk ρ)) (weak (fromWk ρ'))         ∎

fromWk-comp {ρ = keep ρ} {ρ' = skip ρ'} =
  weak (fromWk (compWW ρ ρ'))                          ≡⟨ cong weak (fromWk-comp {ρ = ρ}) ⟩  -- IH
  weak (compSS (fromWk ρ) (fromWk ρ'))                 ≡⟨ sym (weak-compSS) ⟩
  compSS (lift (fromWk ρ)) (weak (fromWk ρ'))          ∎

fromWk-comp {ρ = keep ρ} {ρ' = keep ρ'} = cong (_∙ var zero) (
  weak (fromWk (compWW ρ ρ'))                          ≡⟨ cong weak (fromWk-comp {ρ = ρ}) ⟩  -- IH
  weak (compSS (fromWk ρ) (fromWk ρ'))                 ≡⟨ sym (weak-compSS) ⟩
  compSS (lift (fromWk ρ)) (weak (fromWk ρ'))          ∎)

fromWk-comp {ρ = skip ρ} {ρ' = keep ρ'} =
   weak (fromWk (compWW ρ (keep ρ')))                  ≡⟨ cong weak (fromWk-comp {ρ = ρ}) ⟩  -- IH
   weak (compSS (fromWk ρ) (fromWk (keep ρ')))         ≡⟨ sym (weak-compSS) ⟩
   compSS (lift (fromWk ρ)) (weak (fromWk (keep ρ')))  ≡⟨ cong (_∙ lookup (weak (fromWk ρ)) zero) (

      compSS (lift (fromWk ρ)) (compWS skip1 (weak (fromWk ρ'))) ≡⟨ sym (assocSWS) ⟩
      compSS (compSW (lift (fromWk ρ)) skip1) (weak (fromWk ρ')) ≡⟨ cong (λ σ → compSS σ (weak (fromWk ρ'))) (

        compSW (weak (fromWk ρ)) (keep idW) ≡⟨ comp-S-idW ⟩
        weak (fromWk ρ) ∎) ⟩

      compSS (weak (fromWk ρ)) (weak (fromWk ρ'))
      ∎) ⟩
   (compSS (weak (fromWk ρ)) (weak (fromWk ρ')) ∙ lookup (weak (fromWk ρ)) zero)
   ∎

-- Compositions with fromWk can be simplified

comp-W-fromWk : compWS ρ (fromWk ρ') ≡ fromWk (compWW ρ ρ')
comp-W-fromWk {ρ = ρ} {ρ' = ρ'} =
   compWS ρ (fromWk ρ')           ≡⟨ sym comp-fromWk-S ⟩
   compSS (fromWk ρ) (fromWk ρ')  ≡⟨ sym (fromWk-comp {ρ = ρ}) ⟩
  fromWk (compWW ρ ρ')            ∎

comp-W-idS : compWS ρ idS ≡ fromWk ρ
comp-W-idS {ρ = ρ} =
  compWS ρ idS           ≡⟨⟩
  compWS ρ (fromWk idW)  ≡⟨ comp-W-fromWk ⟩
  fromWk (compWW ρ idW)  ≡⟨ cong fromWk (comp-W-id {ρ = ρ}) ⟩
  fromWk ρ ∎

comp-S-fromWk : compSS σ (fromWk ρ) ≡ compSW σ ρ
comp-S-fromWk {σ = ε}    {ρ = done}   = refl
comp-S-fromWk {σ = σ ∙ t} {ρ = skip ρ} = trans comp-ext-weak comp-S-fromWk
comp-S-fromWk {σ = σ ∙ t} {ρ = keep ρ} = cong (_∙ t) (trans comp-ext-weak comp-S-fromWk)

comp-fromWk-W : compSW (fromWk ρ) ρ' ≡ fromWk (compWW ρ ρ')
comp-fromWk-W {ρ = ρ} {ρ' = ρ'} = sym (trans (fromWk-comp {ρ = ρ}) (comp-S-fromWk {ρ = ρ'}) )

comp-idS-W : compSW idS ρ ≡ fromWk ρ
comp-idS-W {ρ = ρ} =
  compSW idS ρ ≡⟨⟩
  compSW (fromWk idW) ρ ≡⟨ comp-fromWk-W {ρ = idW} ⟩
  fromWk (compWW idW ρ) ≡⟨ cong fromWk (comp-id-W {ρ = idW}) ⟩
  fromWk ρ ∎

-- This lemma is the reason for the whole fromWk business:

comp-id-W-comp-W-id : compSW (idS {Γ = Γ}) ρ ≡ compWS ρ (idS {Γ = Δ})
comp-id-W-comp-W-id {Γ = Γ} {Δ = Δ} {ρ = ρ} = trans comp-idS-W (sym comp-W-idS)

-- compSW (σ ∙ t) (keep ρ)
wk-sg : (wk (keep ρ) t) [ wk ρ u ]₀  ≡ wk ρ (t [ u ]₀)
wk-sg {ρ = ρ} {t = t} {u = u} =
   wk (keep ρ) t [ wk ρ u ]₀              ≡⟨⟩
   sub (idS ∙ wk ρ u) (wk (keep ρ) t)     ≡⟨ sub-wk {ρ = keep ρ} {t = t} ⟩
   sub (compSW (idS ∙ wk ρ u) (keep ρ)) t ≡⟨⟩
   sub (compSW idS ρ ∙ wk ρ u) t          ≡⟨ cong (λ σ → sub (σ ∙ wk ρ u) t) comp-id-W-comp-W-id  ⟩
   sub (compWS ρ (idS ∙ u)) t             ≡⟨ sym (wk-sub {t = t}) ⟩
   wk ρ (sub (idS ∙ u) t)                 ≡⟨⟩
   wk ρ (t [ u ]₀) ∎

compWS-skip1 : compWS (skip1 {a = a}) σ ≡ compSW (lift σ) skip1
compWS-skip1 {σ = σ} = sym (comp-S-idW {ρ = idW})

wk1-sub : wk1 {a = a} (sub σ t) ≡ sub (lift σ) (wk1 t)
wk1-sub {σ = σ} {t = t} =
  wk1 (sub σ t)                  ≡⟨ wk-sub {ρ = skip1} {σ = σ} {t = t} ⟩
  sub (compWS skip1 σ) t         ≡⟨ cong (λ σ → sub σ t) (compWS-skip1 {σ = σ}) ⟩
  sub (compSW (lift σ) skip1) t  ≡⟨ sym (sub-wk {t = t}) ⟩
  sub (lift σ) (wk1 t)  ∎

-- -}
-- -}
-- -}
-- -}
