{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

data FreeCMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeCMon A
  e : FreeCMon A
  _⊕_ : FreeCMon A -> FreeCMon A -> FreeCMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  comm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  trunc : isSet (FreeCMon A)

private
  variable
    ℓ : Level
    A X : Type ℓ

freeCMon-α : sig M.MonSig (FreeCMon X) -> FreeCMon X
freeCMon-α (M.e , _) = e
freeCMon-α (M.⊕ , i) = i fzero ⊕ i fone

𝔉 : (A : Type ℓ) -> struct ℓ M.MonSig
𝔉 A = < FreeCMon A , freeCMon-α >

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where

  module _ (f : A -> 𝔜 .carrier) where
    _♯ : FreeCMon A -> 𝔜 .carrier
    η a ♯ = f a
    e ♯ = 𝔜 .algebra (M.e , lookup [])
    (m ⊕ n) ♯ = 𝔜 .algebra (M.⊕ , lookup (m ♯ ∷ n ♯ ∷ []))
    unitl m i ♯ = {!!}
    unitr m i ♯ = {!!}
    assocr m n o i ♯ = {!!}
    comm m n i ♯ = {!!}
    trunc m n p q i j ♯ = {!!}
