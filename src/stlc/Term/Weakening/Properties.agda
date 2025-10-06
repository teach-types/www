-- Properties of weakenings

module Term.Weakening.Properties where

open import Prelude
open import Term
open import Term.Weakening renaming (lookup to lookupW)

open ≡-Reasoning

private
  variable
    a b : Ty
    Γ Δ Δ₁ Δ₂ Φ : Context
    x : a ∈ Γ
    t : Term Γ a
    ρ ρ' ρ₁ ρ₂ ρ₃ : Wk Γ Δ

-- Inversion properties on weakenings.

-- If  ρ : Wk Γ Δ  then Δ cannot be longer than Γ.
-- In particular, Wk is anti-symmetric and thus a partial order, i.e.,
-- if Wk Γ Δ and Wk Δ Γ then Γ ≡ Δ.
--
-- The proof is not entirely trivial and needs a lemma:
--
-- We first observe that if ρ : Wk Γ (a ∷ Δ) then "a" must appear somewhere in Γ,
-- so Γ is of the form Γ₁ ++ a ∷ Γ₂, and further ρ' : Wk Γ₂ Δ.
-- This means that ρ is obtained from ρ' by one "keep" and zero or more "skip"s.
--
-- The proof is by induction on ρ.
-- If it is a "skip", proceed by induction hypothesis;
-- otherwise it is a "keep", then the proof is immediate.

Wk-cons-inv : Wk Γ (a ∷ Δ) → ∃ λ Γ₁ → ∃ λ Γ₂ → (Γ ≡ Γ₁ ++ a ∷ Γ₂) × Wk Γ₂ Δ
Wk-cons-inv (skip ρ) with Wk-cons-inv ρ
... | Γ₁ , Γ₂ , refl , ρ' = (_ ∷ Γ₁) , _ , refl , ρ'
Wk-cons-inv (keep ρ) = [] , _ , refl , ρ

-- The lemma can be generalized to  ρ : Wk Γ (Δ₁ ++ a ∷ Δ₂).
-- Here, Γ can be decomposed in the same way.
--
-- The proof is by induction on Δ₁, using the previous lemma for the base case Δ₁ = [].

Wk-append-inv : Wk Γ (Δ₁ ++ a ∷ Δ₂) → ∃ λ Γ₁ → ∃ λ Γ₂ → (Γ ≡ Γ₁ ++ a ∷ Γ₂) × Wk Γ₂ Δ₂
Wk-append-inv {Δ₁ = []} ρ = Wk-cons-inv ρ
Wk-append-inv {Δ₁ = a ∷ Δ₁} (skip ρ) with Wk-append-inv {Δ₁ = a ∷ Δ₁} ρ
... | Γ₁ , Γ₂ , refl , ρ' = _ ∷ _ , _ , refl , ρ'
Wk-append-inv {Δ₁ = a ∷ Δ₁} (keep ρ) with Wk-append-inv ρ
... | Γ₁ , Γ₂ , refl , ρ' = _ ∷ _ , _ , refl , ρ'

-- We can now prove that Wk Γ (Δ ++ a ∷ Γ) is impossible.
-- By the previous lemma we get Γ ≡ Γ₁ ++ a ∷ Γ₂ and Wk Γ₂ Γ which is
-- Wk Γ₂ (Γ₁ ++ a ∷ Γ₂).
-- Thus, we are back to what we want to prove, but for Γ₂ which is shorter than Γ.
-- The proof can hence proceed on well-founded induction on Γ (or its length).

-- Agda's termination checker is not powerful enough to automatically follow
-- our argument.
-- Here we decide to take a short-cut and simply switch off the termination
-- checker, relying on our pen-and-paper argument.
-- However, with some more effort we could make the argument completely formal.

{-# TERMINATING #-}
Wk-append : Wk Γ (Δ ++ a ∷ Γ) → ⊥
Wk-append ρ with Wk-append-inv ρ
... | Γ₁ , Γ₂ , refl , ρ' = Wk-append ρ'

-- In particular,  Wk Γ (a ∷ Γ) is impossible, which we knew all along,
-- but the proof of that "trivial" fact required some thinking.

Wk-cons : Wk Γ (a ∷ Γ) → ⊥
Wk-cons ρ = Wk-append {Δ = []} ρ

-- We can now show that weakening is anti-symmetric, i.e.,
-- if  ρ : Wk Γ Δ  and  ρ' : Wk Δ Γ  then Γ ≡ Δ.
-- This is easily shown by induction on ρ and ρ',
-- because the "skip" cases are impossible thanks to Wk-cons.

Wk-anti-sym : Wk Γ Δ → Wk Δ Γ → Γ ≡ Δ
-- "skip" is impossible:
Wk-anti-sym (skip ρ) ρ'        = case Wk-cons (compWW ρ ρ') of λ()
Wk-anti-sym (keep ρ) (skip ρ') = case Wk-cons (compWW ρ ρ') of λ()
-- Diagonal cases are easy:
Wk-anti-sym (keep ρ) (keep ρ') = cong (_ ∷_) (Wk-anti-sym ρ ρ')
Wk-anti-sym  done     done     = refl

-- In fact, if  ρ : Wk Γ Δ  and  ρ' : Wk Δ Γ  then even  ρ ≡ ρ'.
-- However, to formulate this theorem we need to make use of  eq : Γ ≡ Δ,
-- to convert ρ and ρ' to the same type Wk Δ Δ.

Wk-anti-sym-uniq : (ρ : Wk Γ Δ) (ρ' : Wk Δ Γ)
  → ∃ λ (eq : Γ ≡ Δ) → subst (λ Γ → Wk Γ Δ) eq ρ
                     ≡ subst (λ Γ → Wk Δ Γ) eq ρ'
Wk-anti-sym-uniq (skip ρ) ρ'        = case Wk-cons (compWW ρ ρ') of λ()
Wk-anti-sym-uniq (keep ρ) (skip ρ') = case Wk-cons (compWW ρ ρ') of λ()
Wk-anti-sym-uniq (keep ρ) (keep ρ') with Wk-anti-sym-uniq ρ ρ'
... | refl , refl                   = refl , refl
Wk-anti-sym-uniq  done     done     = refl , refl

-- idW behaves as the identity wrt. weakening variables (lookup),
-- terms (wk), and weakenings (compWW).

lookup-idW : lookupW idW x ≡ x
lookup-idW {x = zero}  = refl
lookup-idW {x = suc x} = cong suc lookup-idW

wk-idW : wk idW t ≡ t
wk-idW {t = var x}   = cong var lookup-idW
wk-idW {t = abs t}   = cong abs wk-idW
wk-idW {t = app t u} = cong₂ app wk-idW wk-idW

comp-W-idW : compWW ρ idW ≡ ρ
comp-W-idW {ρ = done}   = refl
comp-W-idW {ρ = skip ρ} = cong skip comp-W-idW
comp-W-idW {ρ = keep ρ} = cong keep comp-W-idW

comp-idW-W : compWW idW ρ ≡ ρ
comp-idW-W {ρ = done}   = refl
comp-idW-W {ρ = skip ρ} = cong skip comp-idW-W
comp-idW-W {ρ = keep ρ} = cong keep comp-idW-W

-- More generally, any ρ : Wk Γ Γ behaves as the identity.
-- We can show that there is only one such ρ for each Γ.
-- This is a special case of our extended anti-symmetry lemma.

idW-unique : (ρ ρ' : Wk Γ Γ) → ρ ≡ ρ'
idW-unique ρ ρ' with Wk-anti-sym-uniq ρ ρ'
... | refl , refl = refl

-- Consequently, we can generalize our lemmata about idW to any ρ : Wk Γ Γ.
-- Wk-cons would be sufficient to prove these generalizations (see Term.Weakening.Properties.Id),
-- but easiest is with idW-unique.

lookup-id : {ρ : Wk Γ Γ} → lookupW ρ x ≡ x
lookup-id {x = x} {ρ = ρ} = subst (λ ρ → lookupW ρ x ≡ x) (idW-unique idW ρ) lookup-idW

wk-id : {ρ : Wk Γ Γ} → wk ρ t ≡ t
wk-id {t = t} {ρ = ρ} = subst (λ ρ → wk ρ t ≡ t) (idW-unique idW ρ) wk-idW

comp-W-id : {ρ' : Wk Γ Γ} → compWW ρ ρ' ≡ ρ
comp-W-id {ρ = ρ} {ρ' = ρ'} = subst (λ ρ' → compWW ρ ρ' ≡ ρ) (idW-unique idW ρ') comp-W-idW

comp-id-W : {ρ : Wk Γ Γ} → compWW ρ ρ' ≡ ρ'
comp-id-W {ρ' = ρ'} {ρ = ρ} = subst (λ ρ → compWW ρ ρ' ≡ ρ') (idW-unique idW ρ) comp-idW-W

-- Composing lookups: looking up a variable in a composition of weakenings
-- is the composition of the lookups.

-- Proof by induction on the first weakening and cases on the second.

lookupW-lookupW : lookupW (compWW ρ ρ') x ≡ lookupW ρ (lookupW ρ' x)
lookupW-lookupW {ρ = skip ρ}                            = cong suc (lookupW-lookupW {ρ = ρ})
lookupW-lookupW {ρ = keep ρ} {ρ' = skip ρ'}             = cong suc (lookupW-lookupW {ρ = ρ})
lookupW-lookupW {ρ = keep ρ} {ρ' = keep ρ'} {x = suc x} = cong suc (lookupW-lookupW {ρ = ρ})
lookupW-lookupW {ρ = keep ρ} {ρ' = keep ρ'} {x = zero}  = refl
lookupW-lookupW {ρ = done}   {ρ' = done}    {x = ()}

-- Composing weakings: applying a composition of weakenings is the composition
-- of the applications.

-- Proof by induction on the term.
-- The interesting case is variables: use lookupW-lookupW here.

wk-wk : wk (compWW ρ ρ') t ≡ wk ρ (wk ρ' t)
wk-wk {t = var x}   = cong var (lookupW-lookupW {x = x})
wk-wk {t = abs t}   = cong abs (wk-wk {t = t})
wk-wk {t = app t u} = cong₂ app wk-wk wk-wk

-- Composition is associative.
-- We do not explicitly require this law, but it makes Wk a category,
-- so we include it here.

-- The proof is shorter if we split the arguments in the right order,
-- so first ρ₁, then ρ₂ only when needed, and same for ρ₃.
-- Only when all three renamings are a "keep" do we get a "keep",
-- any "skip" will propagate to a "skip" on the composition.

assocWWW : compWW (compWW ρ₁ ρ₂) ρ₃ ≡ compWW ρ₁ (compWW ρ₂ ρ₃)
assocWWW {ρ₁ = done}    {ρ₂ = ρ₂}      {ρ₃ = ρ₃}      = refl
assocWWW {ρ₁ = skip ρ₁} {ρ₂ = ρ₂}      {ρ₃ = ρ₃}      = cong skip (assocWWW {ρ₁ = ρ₁})
assocWWW {ρ₁ = keep ρ₁} {ρ₂ = skip ρ₂} {ρ₃ = ρ₃}      = cong skip (assocWWW {ρ₁ = ρ₁})
assocWWW {ρ₁ = keep ρ₁} {ρ₂ = keep ρ₂} {ρ₃ = skip ρ₃} = cong skip (assocWWW {ρ₁ = ρ₁})
assocWWW {ρ₁ = keep ρ₁} {ρ₂ = keep ρ₂} {ρ₃ = keep ρ₃} = cong keep (assocWWW {ρ₁ = ρ₁})

------------------------------------------------------------------------
-- In categorical terms, we have now established that:
--
-- 1. Wk is a directed category ("anti-symmetric")
--    with only identity endomorphism.
--
-- 2. lookup is a functor from Wk to the category of renaming functions
--    (Hom(Γ,Δ) = ∀ a → a ∈ Δ → a ∈ Γ).
--
-- 3. wk is a functor from Wk to the category of substitution functions
--    (Hom(Γ,Δ) = ∀ a → a ∈ Δ → Term Γ a).
------------------------------------------------------------------------

-- A specialized lemma needed for the eta-expansion rule:
-- Permuting a skip1 weakening with an arbitrary weakening.

-- Proven directly from the definitions and established lemmata.

wk1-wk : wk1 {a = a} (wk ρ t) ≡ wk (keep ρ) (wk1 t)
wk1-wk {ρ = ρ} {t = t} =
   wk1 (wk ρ t)                 ≡⟨ sym wk-wk ⟩
   wk (compWW skip1 ρ) t        ≡⟨ cong (λ ρ → wk ρ t) (comp-id-W {ρ = idW}) ⟩
   wk (skip ρ) t                ≡⟨ cong (λ ρ → wk (skip ρ) t) (sym (comp-W-id {ρ' = idW})) ⟩
   wk (compWW (keep ρ) skip1) t ≡⟨ wk-wk ⟩
   wk (keep ρ) (wk1 t) ∎
