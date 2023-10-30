{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List as L renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.LehmerCode
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as EQ
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Set.Mon.Array
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

SymmAction : ∀ {A : Type ℓ} -> Array A -> Array A -> Type ℓ
SymmAction (n , v) (m , w) = Σ[ σ ∈ Iso (Fin n) (Fin m) ] v ≡ w ∘ σ .fun

symm-refl : {as : Array A} -> SymmAction as as
symm-refl {as = as} = idIso , refl

symm-symm : {as bs : Array A} -> SymmAction as bs -> SymmAction bs as
symm-symm {as = as} {bs = bs} (aut , eqn) = invIso aut , sym (funExt lemma)
  where
  lemma : _
  lemma w =
    snd as (inv aut w) ≡⟨ congS (λ f -> f (inv aut w)) eqn ⟩
    snd bs (aut .fun (inv aut w)) ≡⟨ congS (snd bs) (aut .rightInv w) ⟩
    snd bs w ∎

symm-trans : {as bs cs : Array A} -> SymmAction as bs -> SymmAction bs cs -> SymmAction as cs
symm-trans {as = as} {bs = bs} {cs = cs} (p-aut , p-eqn) (q-aut , q-eqn) =
  compIso p-aut q-aut , sym (funExt lemma)
  where
  lemma : _
  lemma w =
    snd cs (q-aut .fun (p-aut .fun w)) ≡⟨ cong (λ f -> f (p-aut .fun w)) (sym q-eqn)  ⟩
    snd bs (p-aut .fun w) ≡⟨ cong (λ f -> f w) (sym p-eqn)  ⟩
    snd as w ∎

module _ {ℓ} (A : Type ℓ) where
  open import Cubical.Relation.Binary
  module P = BinaryRelation {A = Array A} SymmAction
  open isPermRel

  isPermRelPerm : isPermRel arrayDef (SymmAction {A = A})
  P.isEquivRel.reflexive (isEquivRel isPermRelPerm) _ = symm-refl
  P.isEquivRel.symmetric (isEquivRel isPermRelPerm) _ _ = symm-symm
  P.isEquivRel.transitive (isEquivRel isPermRelPerm) _ _ cs = symm-trans {cs = cs}
  isCongruence isPermRelPerm {as} {bs} {cs} {ds} p q = {!   !}
  isCommutative isPermRelPerm = {!   !}
  resp-♯ isPermRelPerm = {!   !}
