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

private
  variable
    ℓ : Level
    A : Type ℓ

SymmAction : ∀ {A : Type ℓ} -> Array A -> Array A -> Type ℓ
SymmAction (n , v) (m , w) = ∃[ σ ∈ Fin n ≃ Fin m ] v ≡ w ∘ σ .fst

compose-equiv : ∀ {A B C : Type ℓ} -> A ≃ B -> B ≃ C -> A ≃ C
compose-equiv p q = equivFun univalence (ua p ∙ ua q)

compose-equiv≡ : ∀ {A B C : Type ℓ} (p : A ≃ B) (q : B ≃ C) (x : A)
               -> equivFun (compose-equiv p q) x ≡ equivFun q (equivFun p x)
compose-equiv≡ {A = A} {B = B} {C = C} p q x =
  _ ≡⟨ sym (transport-filler _ _) ⟩
  fst q (transp (λ i → B) i0 (fst p (transp (λ i → A) i0 x))) ≡⟨ cong (fst q) (sym (transport-filler _ _)) ⟩
  fst q (fst p (transp (λ i → A) i0 x)) ≡⟨ cong (fst q ∘ fst p) (sym (transport-filler _ _)) ⟩
  fst q (fst p x) ∎

symm-refl : {as : Array A} -> SymmAction as as
symm-refl {as = as} = ∣ idEquiv _ , refl ∣₁

symm-symm : {as bs : Array A} -> SymmAction as bs -> SymmAction bs as
symm-symm {as = as} {bs = bs} =
  PT.rec squash₁ λ (aut , eqn) -> ∣ invEquiv aut , sym (funExt (lemma aut eqn)) ∣₁
  where
  lemma : (aut : Fin (fst as) ≃ Fin (fst bs)) -> snd as ≡ snd bs ∘ aut .fst -> (x : Fin (fst bs)) -> _
  lemma aut eqn w =
    snd as (invEquiv aut .fst w) ≡⟨ congS (λ f -> f (invEquiv aut .fst w)) eqn ⟩
    snd bs (aut .fst (invEquiv aut .fst w)) ≡⟨ cong (snd bs) (invEq≡→equivFun≡ aut refl) ⟩
    snd bs w ∎

symm-trans : {as bs cs : Array A} -> SymmAction as bs -> SymmAction bs cs -> SymmAction as cs
symm-trans {as = as} {bs = bs} {cs = cs} =
  PT.rec (isPropΠ λ _ -> squash₁) λ (p-aut , p-eqn) ->
    PT.rec squash₁ λ (q-aut , q-eqn) ->
      ∣ compEquiv p-aut q-aut , sym (funExt (lemma p-aut q-aut p-eqn q-eqn)) ∣₁
  where
  lemma : (p-aut : Fin (fst as) ≃ Fin (fst bs)) -> (q-aut : Fin (fst bs) ≃ Fin (fst cs))
          -> snd as ≡ snd bs ∘ p-aut .fst -> snd bs ≡ snd cs ∘ q-aut .fst -> (x : Fin (fst as))
          -> _
  lemma p-aut q-aut p-eqn q-eqn w =
    snd cs (q-aut .fst (p-aut .fst w)) ≡⟨ cong (λ f -> f (p-aut .fst w)) (sym q-eqn) ⟩
    snd bs (p-aut .fst w) ≡⟨ cong (λ f -> f w) (sym p-eqn)  ⟩
    snd as w ∎

module _ {ℓ} (A : Type ℓ) where
  open import Cubical.Relation.Binary
  module P = BinaryRelation {A = Array A} SymmAction
  open isPermRel

  isPermRelPerm : isPermRel arrayDef (SymmAction {A = A})
  P.isEquivRel.reflexive (isEquivRel isPermRelPerm) _ = symm-refl
  P.isEquivRel.symmetric (isEquivRel isPermRelPerm) _ _ = symm-symm
  P.isEquivRel.transitive (isEquivRel isPermRelPerm) _ _ cs = symm-trans {cs = cs}
  isCongruence isPermRelPerm = {!   !}
  isCommutative isPermRelPerm = {!   !}
  resp-♯ isPermRelPerm = {!   !}
