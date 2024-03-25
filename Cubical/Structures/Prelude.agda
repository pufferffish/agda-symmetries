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

postulate
  TODO : {a : Level} {A : Type a} -> A
