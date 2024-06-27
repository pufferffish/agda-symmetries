{-# OPTIONS --cubical --exact-split #-}

module Cubical.Structures.Prelude where

open import Cubical.Foundations.Prelude public

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

compPath-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square q s (sym p) r)
            → (p ∙∙ q ∙∙ r , doubleCompPath-filler p q r) ≡ β
compPath-contract p q r β = compPath-unique p q r _ β

compPath-unique' : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
           → {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
           → (β : Square q s (sym p) r)
           → s ≡ p ∙∙ q ∙∙ r
compPath-unique' β i = compPath-contract _ _ _ (_ , β) (~ i) .fst

ap-square
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      {a00 a01 a10 a11 : A}
      {p : a00 ≡ a01}
      {q : a10 ≡ a11}
      {r : a01 ≡ a11}
      {s : a00 ≡ a10}
  → (f : A → B)
  → (β : Square p q s r)
  → SquareP (λ i j → B) (ap f p) (ap f q) (ap f s) (ap f r)
ap-square f β i j = f (β i j)

ap-doubleCompPath : (f : A → B) {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
      → ap f (p ∙∙ q ∙∙ r) ≡ ap f p ∙∙ ap f q ∙∙  ap f r
ap-doubleCompPath f p q r = compPath-unique' (ap-square f (doubleCompPath-filler p q r))

ap-compPath : (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-compPath f p q = ap-doubleCompPath f refl p q

postulate
  TODO : {a : Level} {A : Type a} -> A
