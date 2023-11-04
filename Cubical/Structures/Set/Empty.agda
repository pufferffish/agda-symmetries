{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Empty where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
import Cubical.Data.List as L

import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

private
  variable
    ℓ : Level
    A : Type ℓ

empty-α : ∀ (A : Type ℓ) -> sig emptySig A -> A
empty-α _ (x , _) = ⊥.rec x

module EmptyDef = F.Definition emptySig emptyEqSig emptySEq

empty-sat : ∀ (A : Type ℓ) -> < A , empty-α A > ⊨ emptySEq
empty-sat _ eqn ρ = ⊥.rec eqn

module TreeFree {x y : Level} {A : Type x} {𝔜 : struct y emptySig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-empty : 𝔜 ⊨ emptySEq) where  
  𝔗 : struct x emptySig
  𝔗 = < Tree emptySig A , empty-α (Tree emptySig A) >

  module _ (f : A -> 𝔜 .car) where
    _♯ : Tree emptySig A -> 𝔜 .car
    leaf x ♯ = f x

    ♯-isHom : structHom 𝔗 𝔜
    fst ♯-isHom = _♯
    snd ♯-isHom x = ⊥.rec x

  treeEquiv : structHom 𝔗 𝔜 ≃ (A -> 𝔜 .car)
  treeEquiv = isoToEquiv
    ( iso
      (λ g -> g .fst ∘ leaf)
      ♯-isHom (λ g -> refl)
      (λ g -> structHom≡ 𝔗 𝔜 (♯-isHom (g .fst ∘ leaf)) g isSet𝔜 (funExt λ x -> lemma g x))
    )
    where
    lemma : (g : structHom 𝔗 𝔜) (x : Tree emptySig A) -> _
    lemma g (leaf x) = refl

treeDef : ∀ {ℓ ℓ'} -> EmptyDef.Free ℓ ℓ' 2
F.Definition.Free.F treeDef = Tree emptySig
F.Definition.Free.η treeDef = leaf
F.Definition.Free.α treeDef = empty-α (Tree emptySig _)
F.Definition.Free.sat treeDef = empty-sat (Tree emptySig _)
F.Definition.Free.isFree treeDef H ϕ = TreeFree.treeEquiv H ϕ .snd