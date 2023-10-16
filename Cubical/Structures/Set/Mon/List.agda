{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.List where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

-- TODO: Prove List is free monoid on Set

module _ {x} {A : Type x} where
  𝔏 : M.MonStruct
  carrier 𝔏 = List A
  algebra 𝔏 (M.`e , i) = []
  algebra 𝔏 (M.`⊕ , i) = {!!}

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where

  module _ (f : A -> 𝔜 .carrier) where
    module 𝔜 = M.MonSEq 𝔜 𝔜-monoid
    _♯ : List A -> 𝔜 .carrier
    [] ♯ = 𝔜.e
    (x ∷ xs) ♯ = f x 𝔜.⊕ (xs ♯)

    private
      ♯-nil : [] ♯ ≡ 𝔜.e
      ♯-nil = refl

      ♯-++ : ∀ {xs ys} -> (xs ++ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
      ♯-++ = {!!}

    ♯-isMonHom : structHom 𝔏 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = {!!}
