module sec-opt where

open import sec-supplement

open import Relation.Binary.PropositionalEquality
open import Algebra using (CommutativeRing)
open import Algebra.Structures
open import Data.Unit using (⊤ ; tt)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Integer

-- A cooler statement of correct2: prettified-correct2

uniq : Set → Set
uniq A = ∀ {x y : A} → x ≡ y

ext-uniq : ∀ {A B : Set} {f g : A → B} {a b : A} →
  uniq A → f a ≡ g b → f ≡ g
ext-uniq {f = f} {g} {a} {b} U eq = extensionality (λ x →
  begin
    f x
  ≡⟨ cong f U ⟩
    f a
  ≡⟨ eq ⟩
    g b
  ≡⟨ cong g U ⟩
    g x
  ∎) where open ≡-Reasoning

-- Equivalence proofs are unique
≡-uniq : ∀ {A : Set} {a b : A} → uniq (a ≡ b)
≡-uniq = proof where -- Boilerplate
  proof : ∀ {A : Set} {a b : A} → ∀ {p q : a ≡ b} → p ≡ q
  proof {p = refl} {refl} = refl

-- Product of singletons are singletons (for example)
Σ-uniq : ∀ {A : Set} {B : A → Set} →
  uniq A →
  (∀ {a} → uniq (B a)) →
  uniq (Σ A B)
Σ-uniq {A} {B} lhs rhs {a , c} {b , d}
  rewrite lhs {a} {b} = cong (_,_ b) rhs

-- Similarly for pairs.
pair-uniq : ∀ {A : Set} {B : A → Set} →
  uniq A →
  (∀ {a} → uniq (B a)) →
  uniq (Pair A B)
pair-uniq {A} {B} lhs rhs {cons a c} {cons b d}
  rewrite lhs {a} {b} | rhs {b} {c} {d} = refl

-- Similarly for triples.
triple-uniq : ∀ {A : Set} {B : A → Set} {C : (a : A) → B a → Set} →
  uniq A →
  (∀ {a} → uniq (B a)) →
  (∀ {a b} → uniq (C a b)) →
  uniq (Triple A B C)
triple-uniq {A} {B} {C} eq1 eq2 eq3 {cons a c e} {cons b d f}
  rewrite eq1 {a} {b} | eq2 {b} {c} {d} | eq3 {b} {d} {e} {f}
  = refl

-- Irrelevance proofs are uniq
irrelevant-uniq : ∀ {Γ} {S : Vars Γ} {ρ : ΔEnv Γ} →
  uniq (irrelevant S ρ)
irrelevant-uniq {S = ∅} {∅} = refl
irrelevant-uniq {S = lack S} = irrelevant-uniq {S = S}
irrelevant-uniq {S = have S} = Σ-uniq ≡-uniq (irrelevant-uniq {S = S})

-- Validity proofs are (extensionally) unique (as functions)
valid-val-uniq : ∀ {τ} {v : ⟦ τ ⟧} {dv : ΔVal τ} →
  ∀ {p q : valid v dv} → p ≡ q
valid-val-uniq {int} = refl
valid-val-uniq {bag} = refl
valid-val-uniq {σ ⇒ τ} =  ext³ (λ v dv R[v,dv] →
  Σ-uniq (valid-val-uniq {τ}) ≡-uniq)

valid-env-uniq : ∀ {τ Γ} {Δt : ΔTerm Γ τ} {ρ : ΔEnv Γ} →
  uniq (Δt is-valid-for ρ)

valid-env-uniq {Δt = Δint _} = refl
valid-env-uniq {Δt = Δadd Δs Δt} =
  pair-uniq (valid-env-uniq {Δt = Δs}) (valid-env-uniq {Δt = Δt})
valid-env-uniq {Δt = Δminus Δt} = valid-env-uniq {Δt = Δt}
valid-env-uniq {Δt = Δbag _} = refl
valid-env-uniq {Δt = Δunion Δs Δt} =
  pair-uniq (valid-env-uniq {Δt = Δs}) (valid-env-uniq {Δt = Δt})
valid-env-uniq {Δt = Δnegate Δt} = valid-env-uniq {Δt = Δt}
valid-env-uniq {Δt = Δmap₀ s Δs t Δt} =
  pair-uniq (valid-env-uniq {Δt = Δs}) (valid-env-uniq {Δt = Δt})
valid-env-uniq {Δt = Δmap₁ s Δt} =
  pair-uniq (valid-env-uniq {Δt = Δt}) (irrelevant-uniq {S = FV s})
valid-env-uniq {Δt = Δsum Δt} = valid-env-uniq {Δt = Δt}
valid-env-uniq {Δt = Δvar x} = refl
valid-env-uniq {Δt = Δapp Δs t Δt} {ρ} = triple-uniq
  (valid-env-uniq {Δt = Δs})
  (valid-env-uniq {Δt = Δt})
  (λ {Vs} {Vt} → valid-val-uniq {v = ⟦ t ⟧ (ignore ρ)} {⟦ Δt ⟧Δ ρ Vt})
valid-env-uniq {Δt = Δabs Δt} = λ {f} {g} →
  ext³ (λ v Δv R[v,Δv] → valid-env-uniq {Δt = Δt})

prettified-correct2 :  ∀ {τ Γ} {t : Term Γ τ} →
  ∀ {ρ pf₂ pf₀} → ⟦ derive2 t ⟧Δ ρ pf₂ ≡ ⟦ derive t ⟧Δ ρ pf₀

prettified-correct2 {t = t} {ρ} {pf₂} {pf₀} =
  begin
    ⟦ derive2 t ⟧Δ ρ pf₂
  ≡⟨ cong (⟦ derive2 t ⟧Δ ρ)
      (valid-env-uniq {Δt = derive2 t} {x = pf₂} {valid2 t}) ⟩
    ⟦ derive2 t ⟧Δ ρ (valid2 t)
  ≡⟨ correct2 {t = t} ⟩
    ⟦ derive t ⟧Δ ρ (égal t)
  ≡⟨ cong (⟦ derive t ⟧Δ ρ)
      (valid-env-uniq {Δt = derive t} {x = égal t} {pf₀}) ⟩
    ⟦ derive t ⟧Δ ρ pf₀
  ∎ where open ≡-Reasoning


-- Why quotioning against an equivalence relation ~ is hard.
-- There being no easy way to sweep the 2-step transformation
-- under the rug, we have to talk about it.

{-
valid' : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → Set
valid' {int} n Δn = ⊤
valid' {bag} b Δb = ⊤
valid' {σ ⇒ τ} f Δf =
  ∀ (v : ⟦ σ ⟧) (Δv : ⟦ ΔType σ ⟧) (R[v,Δv] : valid' v Δv)
  → valid' (f v) (Δf v Δv)
  × (f ⟦⊕⟧ Δf) (v ⟦⊕⟧ Δv) ≡ f v ⟦⊕⟧ Δf v Δv

infix 4 _~_
_~_ : ∀ {τ} → ⟦ ΔType τ ⟧ → ⟦ ΔType τ ⟧ → Set
_~_ {int} Δm Δn = Δm ≡ Δn
_~_ {bag} Δa Δb = Δa ≡ Δb
_~_ {σ ⇒ τ} Δf Δg =
  ∀ (v : ⟦ σ ⟧) (Δv : ⟦ ΔType σ ⟧) -- (Δw : ⟦ ΔType σ ⟧)
    (R[v,Δv] : valid' v Δv) -- (Δv~Δw : Δv ~ Δw)
    -- → Δf v Δv ~ Δg v Δw
    → Δf v Δv ~ Δg v Δv

f⊕[g⊝f]=g : ∀ {τ : Type} (f g : ⟦ τ ⟧) → f ⟦⊕⟧ (g ⟦⊝⟧ f) ≡ g
f⊕[g⊝f]=g {int} n m = n+[m-n]=m {n} {m}
f⊕[g⊝f]=g {bag} b₁ b₂ = b++[d\\b]=d {b₁} {b₂}
f⊕[g⊝f]=g {τ₁ ⇒ τ₂} f g = extensionality (λ x →
    begin
      (f ⟦⊕⟧ (g ⟦⊝⟧ f)) x
    ≡⟨ refl ⟩
      f x ⟦⊕⟧ (g (x ⟦⊕⟧ (x ⟦⊝⟧ x)) ⟦⊝⟧ f x)
    ≡⟨ cong₂ _⟦⊕⟧_
            {x = f x} {y = f x} refl
            (cong₂ _⟦⊝⟧_ (cong g (f⊕[g⊝f]=g x x)) refl) ⟩
      f x ⟦⊕⟧ (g x ⟦⊝⟧ f x)
    ≡⟨ f⊕[g⊝f]=g (f x) (g x) ⟩
      g x
    ∎
  ) where open ≡-Reasoning

R[f,g⊝f] : ∀ {τ} (f g : ⟦ τ ⟧) → valid' {τ} f (g ⟦⊝⟧ f)
R[f,g⊝f] {int} m n = tt
R[f,g⊝f] {bag} b₁ b₂ = tt
R[f,g⊝f] {τ₁ ⇒ τ₂} f g = λ x dx R[x,dx] →
  R[f,g⊝f] {τ₂} (f x) (g (x ⟦⊕⟧ dx))
  ,
  (begin
    (f ⟦⊕⟧ (g ⟦⊝⟧ f)) (x ⟦⊕⟧ dx)
  ≡⟨ refl ⟩
    f (x ⟦⊕⟧ dx) ⟦⊕⟧
      (g ((x ⟦⊕⟧ dx) ⟦⊕⟧ ((x ⟦⊕⟧ dx) ⟦⊝⟧ (x ⟦⊕⟧ dx))) ⟦⊝⟧ f (x ⟦⊕⟧ dx))
  ≡⟨ cong (λ hole → f (x ⟦⊕⟧ dx) ⟦⊕⟧ (g hole ⟦⊝⟧ f (x ⟦⊕⟧ dx)))
          (f⊕[g⊝f]=g (x ⟦⊕⟧ dx) (x ⟦⊕⟧ dx)) ⟩
    f (x ⟦⊕⟧ dx) ⟦⊕⟧ (g (x ⟦⊕⟧ dx) ⟦⊝⟧ f (x ⟦⊕⟧ dx))
  ≡⟨ f⊕[g⊝f]=g (f (x ⟦⊕⟧ dx)) (g (x ⟦⊕⟧ dx)) ⟩
    g (x ⟦⊕⟧ dx)
  ≡⟨ sym (f⊕[g⊝f]=g (f x) (g (x ⟦⊕⟧ dx))) ⟩
      f x ⟦⊕⟧ (g ⟦⊝⟧ f) x dx
  ∎)
  where open ≡-Reasoning

-- "carry-over"
co : ∀ {τ} {v : ⟦ τ ⟧} {Δv : ⟦ ΔType τ ⟧} {Δw : ⟦ ΔType τ ⟧} →
  Δv ~ Δw → v ⟦⊕⟧ Δv ≡ v ⟦⊕⟧ Δw

co {int} {v} Δv~Δw = cong (_⟦⊕⟧_ v) Δv~Δw
co {bag} {v} Δv~Δw = cong (_⟦⊕⟧_ v) Δv~Δw
co {σ ⇒ τ} {f} {Δf} {Δg} Δf~Δg = extensionality (λ v →
  co {τ} {f v} {Δf v (v ⟦⊝⟧ v)} {Δg v (v ⟦⊝⟧ v)}
    (Δf~Δg v (v ⟦⊝⟧ v) (R[f,g⊝f] v v)))

~-comm : ∀ {τ} {Δv : ⟦ ΔType τ ⟧} {Δw : ⟦ ΔType τ ⟧} →
  Δv ~ Δw → Δw ~ Δv
~-comm {int} Δv=Δw = sym Δv=Δw
~-comm {bag} Δv=Δw = sym Δv=Δw
~-comm {σ ⇒ τ} Δf~Δg = λ v Δv R[v,Δv] →
  ~-comm {τ} (Δf~Δg v Δv R[v,Δv])

cv : ∀ {τ} {v : ⟦ τ ⟧} {Δv : ⟦ ΔType τ ⟧} {Δw : ⟦ ΔType τ ⟧} →
  Δv ~ Δw → valid' v Δv → valid' v Δw

cv {int} _ _ = tt
cv {bag} _ _ = tt
cv {σ ⇒ τ} {f} {Δf} {Δg} Δf~Δg Vf = λ v Δv R[v,Δv] →
  cv {τ} {f v} (Δf~Δg v Δv R[v,Δv]) (proj₁ (Vf v Δv R[v,Δv]))
  ,
  (begin
    (f ⟦⊕⟧ Δg) (v ⟦⊕⟧ Δv)
  ≡⟨ cong (λ hole → hole (v ⟦⊕⟧ Δv))
       (co {σ ⇒ τ} {f} {Δg} {Δf} (~-comm {Δv = Δf} {Δg} Δf~Δg)) ⟩
    (f ⟦⊕⟧ Δf) (v ⟦⊕⟧ Δv)
  ≡⟨ proj₂ (Vf v Δv R[v,Δv]) ⟩
    f v ⟦⊕⟧ Δf v Δv
  ≡⟨ co {τ} {f v} {Δf v Δv} {Δg v Δv} (Δf~Δg v Δv R[v,Δv]) ⟩
    f v ⟦⊕⟧ Δg v Δv
  ∎) where open ≡-Reasoning

consistent : ∀ {Γ} → ⟦ ΔContext Γ ⟧ → Set
consistent {∅} ∅ = ⊤
consistent {τ • Γ} (Δv • v • ρ) = valid' v Δv × consistent ρ

opt : ∀ {τ Γ} (t : Term Γ τ)
  {ρ : ⟦ ΔContext Γ ⟧} (C : consistent ρ) →
  ⟦ incrementalize t ⟧ ρ ~ ⟦ opt-incrementalize t ⟧ ρ

Δv~Δv : ∀ {τ} {Δv : ⟦ ΔType τ ⟧} → Δv ~ Δv
Δv~Δv {int} = refl
Δv~Δv {bag} = refl
Δv~Δv {σ ⇒ τ} {Δf} = λ v Δv R[v,Δv] → Δv~Δv {τ} {Δf v Δv}

opt (int n) C = refl
opt (add s t) C = cong₂ _+_ (opt s C) (opt t C)
opt (minus t) C = cong -_ (opt t C)
opt (bag b) C = refl
opt (union s t) C = cong₂ _++_ (opt s C) (opt t C)
opt (negate t) C = cong negateBag (opt t C)

opt (map s t) {ρ} C with closed? s
... | inj₁ when-closed =
  let
    f = ⟦ fit s ⟧ ρ
    b = ⟦ fit t ⟧ ρ
    Δf = ⟦ incrementalize s ⟧ ρ
    Δb = ⟦ incrementalize t ⟧ ρ
    Δb′ = ⟦ opt-incrementalize t ⟧ ρ

    eq2 : mapBag (f ⟦⊕⟧ Δf) (b ⟦⊕⟧ Δb) ⟦⊝⟧ mapBag f b
        ≡ mapBag f Δb
    eq2 = trans
      (cong (λ hole → hole ⟦⊝⟧ mapBag f b) (trans
        (cong (λ hole → mapBag hole (b ⟦⊕⟧ Δb))
          {!just project stability it's gonna be fine!}
          -- (stability {t = s} I)
          )
        homo-map))
      [b++d]\\b=d

  in
    begin
      mapBag (f ⟦⊕⟧ Δf) (b ⟦⊕⟧ Δb) ⟦⊝⟧ mapBag f b
    ≡⟨ eq2 ⟩
      mapBag f Δb
    ≡⟨ cong (mapBag f) (opt t C) ⟩
      mapBag f Δb′
    ∎
  where
  open ≡-Reasoning

... | inj₂ tt =
  cong₂ _\\_
    (cong₂ mapBag
      (co {v = ⟦ fit s ⟧ ρ} (opt s C))
      (co {v = ⟦ fit t ⟧ ρ} (opt t C)))
    refl

opt (sum t) C = cong sumBag (opt t C)
opt {τ} (var x) {ρ} C = Δv~Δv {τ} {⟦ embedΔVar x ⟧ ρ}
opt (app s t) C = {!OGOTTOGOTT!}
opt (abs t) C = {!!}
-}
