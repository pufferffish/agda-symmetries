{-# OPTIONS --cubical #-}
module Cubical.Structures.Inspect where

open import Cubical.Foundations.Everything
open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ' : Level

-- We are currently using cubical v0.5 which doesn't have
-- dependent inspect yet.
-- The cubical commit 3202e3891db2bf907a95fde1202112eba517989d adds it,
-- so we can remove this file once we update to that version.
module _ {A : Type ℓ} {B : A -> Type ℓ'} where

  record DReveal_·_is_ (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ-max ℓ ℓ') where
    constructor [_]ᵢ
    field path : f x ≡ y

  inspect' : (f : (x : A) → B x) (x : A) → DReveal f · x is f x
  inspect' f x .DReveal_·_is_.path = refl

-- From: https://stackoverflow.com/questions/74733455/agda-confusion-with-inspect
data OldInspect {A : Type ℓ} (x : A) : Type ℓ where
  _with-≡_ : (y : A) (eq : x ≡ y) → OldInspect x

oldInspect : ∀ {A : Type ℓ} (x : A) → OldInspect x
oldInspect x = x with-≡ refl