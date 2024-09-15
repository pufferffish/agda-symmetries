{-# OPTIONS --cubical --exact-split #-}

module Cubical.Structures.Prelude where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Everything
open import Cubical.Relation.Nullary.Base
import Cubical.Data.Empty as ⊥
import Cubical.HITs.PropositionalTruncation as P

private
  variable
    ℓ : Level
    A B C : Type ℓ
    x y z w : A

idp : (x : A) → x ≡ x
idp x = refl

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap = congS

ap₂ : (f : A → B → C) → x ≡ y → z ≡ w → f x z ≡ f y w
ap₂ f p q i = f (p i) (q i)

module _ {ℓ ℓ'} {P : Type ℓ} {A : Dec P → Type ℓ'} where

  decElim : ((p : P) → A (yes p)) → ((¬p : ¬ P) → A (no ¬p))
          → (p : Dec P) → A p
  decElim y n (yes p) = y p
  decElim y n (no ¬p) = n ¬p

module _ {ℓ} {P : Type ℓ} (isPropP : isProp P) where

  private
    isPropDec : isProp (Dec P)
    isPropDec (yes p) (yes q) = congS yes (isPropP p q)
    isPropDec (yes p) (no ¬q) = ⊥.rec (¬q p)
    isPropDec (no ¬p) (yes q) = ⊥.rec (¬p q)
    isPropDec (no ¬p) (no ¬q) = congS no (isProp→ ⊥.isProp⊥ ¬p ¬q)

  decRec-yes : {y : P -> A} {n : ¬ P -> A} (p : P) (d : Dec P) -> decRec y n d ≡ y p
  decRec-yes {y = y} {n = n} p = decElim (λ q -> congS y (isPropP q p)) λ ¬p -> ⊥.rec (¬p p)

  decRec-no : {y : P -> A} {n : ¬ P -> A} (¬p : ¬ P) (d : Dec P) -> decRec y n d ≡ n ¬p
  decRec-no {y = y} {n = n} ¬p = decElim (λ p -> ⊥.rec (¬p p)) (λ ¬q -> congS n (isProp→ ⊥.isProp⊥ ¬q ¬p))

module Toset {ℓ : Level} {A : Type ℓ} where
  open import Cubical.Relation.Binary.Order
  open import Cubical.Data.Sigma as S
  open import Cubical.Data.Sum as ⊎
  open import Cubical.Functions.Logic using (_⊔′_)

  IsDecOrder : (A -> A -> Type ℓ) -> Type _
  IsDecOrder _≤_ = IsToset _≤_ × (∀ x y -> Dec (x ≤ y))

  HasDecOrder : Type _
  HasDecOrder = Σ _ IsDecOrder

  open IsToset
  decOrd→disc : (_≤_ : A -> A -> Type ℓ) -> IsDecOrder (_≤_) -> Discrete A
  decOrd→disc _≤_ (tosetA , _≤?_) x y with x ≤? y | y ≤? x
  ... | yes p | yes q = yes (tosetA .is-antisym x y p q)
  ... | yes p | no ¬q = no λ r -> ¬q (subst (_≤ x) r (tosetA .is-refl x))
  ... | no ¬p | yes q = no λ r -> ¬p (subst (x ≤_) r (tosetA .is-refl x))
  ... | no ¬p | no ¬q = ⊥.rec (P.rec ⊥.isProp⊥ (⊎.rec ¬p ¬q) (tosetA .is-strongly-connected x y))

  toset-≰→≤ : (_≤_ : A -> A -> Type ℓ) -> IsToset (_≤_) -> ∀ x y -> ¬ (x ≤ y) -> (y ≤ x)
  toset-≰→≤ _≤_ tosetA x y ¬p =
    P.rec (tosetA .is-prop-valued y x)
          (⊎.rec (λ x≤y -> ⊥.rec (¬p x≤y)) (λ y≤x -> y≤x))
          (tosetA .is-strongly-connected x y)

  module Toset-⋀ (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

    ⋀-f : (a b : A) -> (a ≤ b) ⊎ (b ≤ a) -> A
    ⋀-f a b = ⊎.rec (λ a≤b -> a) (λ b≤a -> b)

    ⋀-f-const : (a b : A) -> 2-Constant (⋀-f a b)
    ⋀-f-const a b =
      ⊎.elim (λ a≤b -> ⊎.elim (λ _ -> refl) (λ b≤a -> tosetA .is-antisym a b a≤b b≤a))
             (λ b≤a -> ⊎.elim (λ a≤b -> tosetA .is-antisym b a b≤a a≤b) (λ _ -> refl))

    _⋀_ : A -> A -> A
    a ⋀ b = P.rec→Set isSetA (⋀-f a b) (⋀-f-const a b) (tosetA .is-strongly-connected a b)

    ⋀-β₁ : ∀ {a b} -> a ≤ b -> (a ⋀ b) ≡ a
    ⋀-β₁ {a = a} {b = b} a≤b =
      P.SetElim.helper isSetA (⋀-f a b) (⋀-f-const a b) (tosetA .is-strongly-connected a b) P.∣ inl a≤b ∣₁

    ⋀-β₂ : ∀ {a b} -> b ≤ a -> (a ⋀ b) ≡ b
    ⋀-β₂ {a = a} {b = b} b≤a =
      P.SetElim.helper isSetA (⋀-f a b) (⋀-f-const a b) (tosetA .is-strongly-connected a b) P.∣ inr b≤a ∣₁

    ⋀-π₁ : ∀ {a b} -> (a ⋀ b) ≤ a
    ⋀-π₁ {a = a} {b = b} =
      P.rec (tosetA .is-prop-valued (a ⋀ b) a) (⊎.rec (λ a≤b -> subst (_≤ a) (sym (⋀-β₁ a≤b)) (tosetA .is-refl a))
                                                      (λ b≤a -> subst (_≤ a) (sym (⋀-β₂ b≤a)) b≤a))
            (tosetA .is-strongly-connected a b)

    ⋀-π₂ : ∀ {a b} -> (a ⋀ b) ≤ b
    ⋀-π₂ {a = a} {b = b} =
      P.rec (tosetA .is-prop-valued (a ⋀ b) b) (⊎.rec (λ a≤b -> subst (_≤ b) (sym (⋀-β₁ a≤b)) a≤b)
                                                      (λ b≤a -> subst (_≤ b) (sym (⋀-β₂ b≤a)) (tosetA .is-refl b)))
            (tosetA .is-strongly-connected a b)

    ⋀-η₁ : ∀ {a b} -> (a ⋀ b) ≡ a -> a ≤ b
    ⋀-η₁ {a = a} {b = b} =
      P.rec (isProp→ (tosetA .is-prop-valued a b))
            (⊎.rec (λ a≤b _ -> a≤b) (λ b≤a ϕ -> subst (_≤ b) ϕ ⋀-π₂))
            (tosetA .is-strongly-connected a b)

    ⋀-univ-fwd : ∀ {x a b} -> x ≤ (a ⋀ b) -> (x ≤ a) × (x ≤ b)
    ⋀-univ-fwd {x = x} {a = a} {b = b} ϕ =
      tosetA .is-trans x (a ⋀ b) a ϕ ⋀-π₁ , tosetA .is-trans x (a ⋀ b) b ϕ ⋀-π₂

    ⋀-univ-bwd : ∀ {x a b} -> (x ≤ a) × (x ≤ b) -> x ≤ (a ⋀ b)
    ⋀-univ-bwd {x = x} {a = a} {b = b} (ϕ , ψ) =
      P.rec (tosetA .is-prop-valued x (a ⋀ b))
            (⊎.rec (λ a≤b -> subst (x ≤_) (sym (⋀-β₁ a≤b)) ϕ)
                   (λ b≤a -> subst (x ≤_) (sym (⋀-β₂ b≤a)) ψ))
            (tosetA .is-strongly-connected a b)

    ⋀-univ : ∀ {x a b} -> (x ≤ (a ⋀ b)) ≃ (x ≤ a) × (x ≤ b)
    ⋀-univ = propBiimpl→Equiv (tosetA .is-prop-valued _ _) (isProp× (tosetA .is-prop-valued _ _) (tosetA .is-prop-valued _ _)) ⋀-univ-fwd ⋀-univ-bwd

    ⋀-idem : ∀ a -> a ⋀ a ≡ a
    ⋀-idem a = ⋀-β₁ (tosetA .is-refl a)

    よ-≡ : ∀ a b -> (∀ x -> x ≤ a ≃ x ≤ b) -> a ≡ b
    よ-≡ a b f = tosetA .is-antisym a b (f a .fst (tosetA .is-refl a)) (invEq (f b) (tosetA .is-refl b))

    ⋀-comm : ∀ a b -> a ⋀ b ≡ b ⋀ a
    ⋀-comm a b = よ-≡ (a ⋀ b) (b ⋀ a) λ x -> compEquiv ⋀-univ (compEquiv Σ-swap-≃ (invEquiv ⋀-univ))

    ⋀-assocr : ∀ a b c -> (a ⋀ b) ⋀ c ≡ a ⋀ (b ⋀ c)
    ⋀-assocr a b c =
      よ-≡ ((a ⋀ b) ⋀ c) (a ⋀ (b ⋀ c))
        λ x -> compEquiv ⋀-univ
                         (compEquiv (Σ-cong-equiv ⋀-univ (λ _ -> idEquiv (x ≤ c)))
                                    (compEquiv Σ-assoc-≃ (compEquiv (Σ-cong-equiv (idEquiv (x ≤ a)) λ _ -> invEquiv ⋀-univ)
                                                                                  (invEquiv ⋀-univ))))

    ⋀-total : ∀ a b -> (a ⋀ b ≡ a) ⊔′ (b ⋀ a ≡ b)
    ⋀-total a b = P.map (⊎.map ⋀-β₁ ⋀-β₁) (tosetA .is-strongly-connected a b)

  module Toset-⋁ (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

    ⋁-f : (a b : A) -> (a ≤ b) ⊎ (b ≤ a) -> A
    ⋁-f a b = ⊎.rec (λ a≤b -> b) (λ b≤a -> a)

    ⋁-f-const : (a b : A) -> 2-Constant (⋁-f a b)
    ⋁-f-const a b = ⊎.elim (λ a≤b -> ⊎.elim (λ _ -> refl) λ b≤a -> tosetA .is-antisym b a b≤a a≤b)
                            (λ b≤a -> ⊎.elim (λ a≤b -> tosetA .is-antisym a b a≤b b≤a) λ _ -> refl)

    _⋁_ : A -> A -> A
    a ⋁ b = P.rec→Set isSetA (⋁-f a b) (⋁-f-const a b) (tosetA .is-strongly-connected a b)

    ⋁-β₁ : ∀ {a b} -> a ≤ b -> (a ⋁ b) ≡ b
    ⋁-β₁ {a = a} {b = b} a≤b = P.SetElim.helper isSetA (⋁-f a b) (⋁-f-const a b) (tosetA .is-strongly-connected a b) P.∣ inl a≤b ∣₁

    ⋁-β₂ : ∀ {a b} -> b ≤ a -> (a ⋁ b) ≡ a
    ⋁-β₂ {a = a} {b = b} b≤a = P.SetElim.helper isSetA (⋁-f a b) (⋁-f-const a b) (tosetA .is-strongly-connected a b) P.∣ inr b≤a ∣₁

    ⋁-π₁ : ∀ {a b} -> a ≤ (a ⋁ b)
    ⋁-π₁ {a = a} {b = b} = P.rec (tosetA .is-prop-valued a (a ⋁ b))
                                  (⊎.rec (λ a≤b -> subst (a ≤_) (sym (⋁-β₁ a≤b)) a≤b)
                                         (λ b≤a -> subst (a ≤_) (sym (⋁-β₂ b≤a)) (is-refl tosetA a)))
                                  (tosetA .is-strongly-connected a b)

    ⋁-π₂ : ∀ {a b} -> b ≤ (a ⋁ b)
    ⋁-π₂ {a = a} {b = b} = P.rec (tosetA .is-prop-valued b (a ⋁ b))
                                  (⊎.rec (λ a≤b -> subst (b ≤_) (sym (⋁-β₁ a≤b)) (is-refl tosetA b))
                                         (λ b≤a -> subst (b ≤_) (sym (⋁-β₂ b≤a)) b≤a))
                                 (tosetA .is-strongly-connected a b)

    ⋁-η₂ : ∀ {a b} -> (a ⋁ b) ≡ b -> a ≤ b
    ⋁-η₂ {a = a} {b = b} =
      P.rec (isProp→ (tosetA .is-prop-valued a b))
            (⊎.rec (λ a≤b _ -> a≤b)
                   (λ b≤a ϕ -> subst (a ≤_) ϕ ⋁-π₁))
            (tosetA .is-strongly-connected a b)

    -- ⋁-univ-fwd : ∀ {x a b} -> (a ⋁ b) ≤ x -> (a ≤ x) × (b ≤ x)
    -- ⋁-univ-bwd : ∀ {x a b} -> (a ≤ x) × (b ≤ x) -> (a ⋁ b) ≤ x
    -- ⋁-univ : ∀ {x a b} -> (a ⋁ b ≤ x) ≃ (a ≤ x) × (b ≤ x)

    ⋁-idem : ∀ a -> a ⋁ a ≡ a
    ⋁-idem a = ⋁-β₁ (tosetA .is-refl a)

    よ-≡ : ∀ a b -> (∀ x -> a ≤ x ≃ b ≤ x) -> a ≡ b
    よ-≡ a b f = tosetA .is-antisym a b (invEq (f b) (tosetA .is-refl b)) (f a .fst (is-refl tosetA a))

    postulate ⋁-comm : ∀ a b -> a ⋁ b ≡ b ⋁ a

    -- ⋁-assocr : ∀ a b c -> (a ⋁ b) ⋁ c ≡ a ⋁ (b ⋁ c)
    -- ⋁-total : ∀ a b -> (a ⋁ b ≡ b) ⊔′ (b ⋁ a ≡ a)

  module ⋀-Toset (isSetA : isSet A) (_⋀_ : A -> A -> A)
                 (⋀-idem : ∀ a -> a ⋀ a ≡ a) (⋀-comm : ∀ a b -> a ⋀ b ≡ b ⋀ a)
                 (⋀-assocr : ∀ a b c -> (a ⋀ b) ⋀ c ≡ a ⋀ (b ⋀ c)) (⋀-total : ∀ a b -> (a ⋀ b ≡ a) ⊔′ (b ⋀ a ≡ b)) where

    _≤_ : A -> A -> Type ℓ
    a ≤ b = (a ⋀ b) ≡ a

    tosetA : IsToset _≤_
    tosetA .is-set = isSetA
    tosetA .is-prop-valued a b = isSetA (a ⋀ b) a
    tosetA .is-refl = ⋀-idem
    tosetA .is-trans a b c a∧b≡a b∧c≡b = congS (_⋀ c) (sym a∧b≡a) ∙ ⋀-assocr a b c ∙ congS (a ⋀_) b∧c≡b ∙ a∧b≡a
    tosetA .is-antisym a b a∧b≡a b∧a≡a = sym a∧b≡a ∙ ⋀-comm a b ∙ b∧a≡a
    tosetA .is-strongly-connected = ⋀-total

  module Toset-⋀-Toset (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

    module Tos-⋀ = Toset-⋀ isSetA _≤_ tosetA
    module ⋀-Tos = ⋀-Toset isSetA Tos-⋀._⋀_ Tos-⋀.⋀-idem Tos-⋀.⋀-comm Tos-⋀.⋀-assocr Tos-⋀.⋀-total

    eq : TosetEquiv (toset A _≤_ tosetA) (toset A ⋀-Tos._≤_ ⋀-Tos.tosetA)
    eq .fst = idEquiv ⟨ toset A _≤_ tosetA ⟩
    eq .snd = istosetequiv λ a b -> propBiimpl→Equiv (tosetA .is-prop-valued a b) (isSetA _ _) Tos-⋀.⋀-β₁ Tos-⋀.⋀-η₁
