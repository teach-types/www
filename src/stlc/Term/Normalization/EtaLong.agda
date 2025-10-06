-- Normalization theorem:
-- Show that each typed term has an η-long β-normal form.

module Term.Normalization.EtaLong where

open import Prelude
open import Term
open import Term.Weakening renaming (lookup to lookupR)
open import Term.Substitution
open import Term.Equality

open import Term.Weakening.Properties    using (wk-id; wk-wk)
open import Term.Substitution.Properties using (sub-id; sub-S-sg)

private
  variable
    Γ Δ Φ : Context
    α : BaseTy
    a b : Ty
    x : a ∈ Γ
    t t' t'' u u' : Term Γ a
    σ σ' : Sub Γ Δ
    ρ : Wk Γ Δ

-- Long normal forms, defined inductively.

mutual

  -- Neutrals: no λ in the head.
  -- Neutrals do not β-reduce
  -- and do not cause β-redexes when replacing a variable in a term.

  data Ne : Term Γ a → Set where
    var : Ne (var x)
    app : Ne t → Nf u → Ne (app t u)

  -- Normal forms: only neutral applications.
  -- For long normal forms, each neutral term is of base type.

  data Nf : Term Γ a → Set where
    ne  : {t : Term Γ (` α)} → Ne t → Nf t
    abs : Nf t → Nf (abs t)


-- Weakly normalizing terms are equal to a normal form.
-- For "wn t" we can also say "t has a normal form".

record wne (t : Term Γ a) : Set where
  constructor wneu
  field
    nf   : Term Γ a
    neu  : Ne nf
    reds : t ≅ nf

record wn (t : Term Γ a) : Set where
  constructor wnorm
  field
    nf : Term Γ a
    norm : Nf nf
    reds : t ≅ nf

-- wn/wne have the same closure properties as normal form,
-- plus they are closed under equality.

mutual
  wne-var : wne (var x)
  wne-var = wneu _ var refl

  wne-app : wne t → wn u → wne (app t u)
  wne-app (wneu _ neu rt) (wnorm _ nf ru) = wneu _ (app neu nf) (app rt ru)

  wn-abs  : wn t → wn (abs t)
  wn-abs (wnorm _ nf rs) = wnorm _ (abs nf) (abs rs)

  wne→wn  : {t : Term Γ (` α)} → wne t → wn t
  wne→wn (wneu _ neu rs) = wnorm _ (ne neu) rs

  expand-wn : t ≅ t' → wn  t' → wn  t
  expand-wn w (wnorm _ nf rs) = wnorm _ nf (≅trans w rs)

-- We cannot directly show that each well-typed term has a normal form,
-- since this property is not closed under application a priori.
--
-- A counterexample does not exist, since they are closed under application
-- a posteriori, but it exists in untyped lambda-calculus:
-- With δ = λ x → x x we have wn δ, but not wn (δ δ).
--
-- To get  wn t → wn u → wn (app t u)  we need to prove something
-- stronger about well-typed terms, namely that they are "reducible".

-- Reducibility:  Interpreting types as sets of weakly normalizing terms.
--
-- In the case of function types, we also require that terms behave
-- as "functions" meaning that they map reducible arguments to reducible results.
--
-- In that, we need to consider reducible arguments in a larger context
-- as we need to be able to apply a λ-term Term Γ (a ⇒ b)
-- to a new fresh variable a ∈ (a ∷ Γ) to show that it is weakly normalizing.
--
-- So, a term of base type is reducible if it is weakly normalizing.
-- A term t : Term Γ (a ⇒ b) of function type is reducible if for each
-- weakening ρ : Wk Δ Γ and each reducible argument u : Term Δ a
-- the application app (wk ρ t) u of the transported term t to u is reducible.

mutual
  Red : (Γ : Context) (a : Ty) (t : Term Γ a) → Set
  Red Γ (` α)   t = wn t
  Red Γ (a ⇒ b) t = ∀{Δ} (ρ : Wk Δ Γ) {u : Term Δ a} (⟦u⟧ : Red Δ a u) → Red Δ b (app (wk ρ t) u)

-- Reducibility for substitutions: a substitution is reducible if each of its terms is reducible.

data Reds Γ : (Δ : Context) (σ : Sub Γ Δ) → Set where
  []  : Reds Γ [] []
  _∷_ : (⟦t⟧ : Red Γ a t) (⟦σ⟧ : Reds Γ Δ σ) → Reds Γ (a ∷ Δ) (t ∷ σ)

-- Projecting a term from a reducible substitution.

⟦lookup⟧ : (⟦σ⟧ : Reds Γ Δ σ) (x : a ∈ Δ) → Red Γ a (lookup σ x)
⟦lookup⟧ (⟦t⟧ ∷ _) zero    = ⟦t⟧
⟦lookup⟧ (_ ∷ ⟦σ⟧) (suc x) = ⟦lookup⟧ ⟦σ⟧ x

-- Reducibility is closed under weak-head expansion.
-- Proof by induction on the type.

expand-Red : t ≅ t' → Red Γ a t' → Red Γ a t
expand-Red {a = ` α}   w wn       = expand-wn w wn
expand-Red {a = a ⇒ b} w ⟦t⟧ ρ ⟦u⟧ = expand-Red (app (wk-≅ w) refl) (⟦t⟧ ρ ⟦u⟧)

-- Normal forms are closed under weakening.
-- Proof by induction on the normal form.

mutual
  wk-Ne : (neu : Ne t) → Ne (wk ρ t)
  wk-Ne var = var
  wk-Ne (app neu norm) = app (wk-Ne neu) (wk-Nf norm)

  wk-Nf : (norm : Nf t) → Nf (wk ρ t)
  wk-Nf (ne neu) = ne (wk-Ne neu)
  wk-Nf (abs norm) = abs (wk-Nf norm)

-- wn and wne are closed under weakening.

wk-wne : wne t → wne (wk ρ t)
wk-wne (wneu _ neu e) = wneu _ (wk-Ne neu) (wk-≅ e)

wk-wn : wn t → wn (wk ρ t)
wk-wn (wnorm _ norm e) = wnorm _ (wk-Nf norm) (wk-≅ e)

-- Reducibility is closed under weakening.
-- Proof by induction on the type.

wk-Red : Red Γ a t → Red Δ a (wk ρ t)
wk-Red {a = ` α}           wn        = wk-wn wn
wk-Red {a = a ⇒ b} {ρ = ρ} ⟦t⟧ ρ' ⟦u⟧ =
  subst
    (λ t → Red _ _ (app t _))
    (wk-wk)
    (⟦t⟧ (compWW ρ' ρ) ⟦u⟧)

-- Reducible substitutions are closed under weakening.
-- Proven pointwise.

wk-Reds : Reds Δ Γ σ → Reds Φ Γ (compWS ρ σ)
wk-Reds [] = []
wk-Reds (⟦t⟧ ∷ ⟦σ⟧) = wk-Red ⟦t⟧ ∷ wk-Reds ⟦σ⟧

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

valid-abs : {t : Term (a ∷ Γ) b} → Valid t → Valid (abs t)
valid-abs {a = a} {Γ = Γ} {b = b} {t = t} ⟦t⟧ {σ = σ} ⟦σ⟧ ρ {u = u} ⟦u⟧ =
  expand-Red
    (subst
      (app (wk ρ (sub σ (abs t))) u ≅_)
      (sub-S-sg {ρ = ρ} {σ = σ} {t = t} {u = u})
      β)
    (⟦t⟧ {σ = u ∷ compWS ρ σ} (⟦u⟧ ∷ wk-Reds ⟦σ⟧))

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
  wne→Red : {t : Term Γ a} → wne t → Red Γ a t
  wne→Red {a = ` α}   wne      = wne→wn wne
  wne→Red {a = a ⇒ b} ⟦t⟧ ρ ⟦u⟧ = wne→Red (wne-app (wk-wne ⟦t⟧) (Red→wn ⟦u⟧))

  Red→wn : {t : Term Γ a} → Red Γ a t → wn t
  Red→wn {a =   ` α} wn = wn
  Red→wn {a = a ⇒ b} ⟦t⟧ = expand-wn η (wn-abs (Red→wn (⟦t⟧ skip1 ⟦var0⟧)))

  ⟦var0⟧ : Red (a ∷ Γ) a (var zero)
  ⟦var0⟧ {a = a} = wne→Red wne-var

-- The identity substitution is reducible.

⟦idS⟧ : Reds Γ Γ idS
⟦idS⟧ {Γ = []}    = []
⟦idS⟧ {Γ = a ∷ Γ} = ⟦var0⟧ ∷ wk-Reds ⟦idS⟧

-- Normalization theorem: each well-typed term t is weakly normalizing.
--
-- Proof steps:
-- * t is valid by the fundamental theorem.
-- * sub idS t is reducible by instantiation with the identity substitution.
-- * sub idS t is weakly normalizing.
-- * t is weakly normalizing.

normalization : (t : Term Γ a) → wn t
normalization t = subst wn (sub-id) (Red→wn (fund t ⟦idS⟧))

-- Q.E.D.




-- Not used: Reducible substitutions are closed under lifting.

⟦lift⟧ : (⟦σ⟧ : Reds Δ Γ σ) → Reds (a ∷ Δ) (a ∷ Γ) (lift σ)
⟦lift⟧ ⟦σ⟧ = ⟦var0⟧ ∷ wk-Reds ⟦σ⟧
