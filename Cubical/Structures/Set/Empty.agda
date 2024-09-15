{-# OPTIONS --cubical --safe --exact-split #-}

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
    ℓ ℓ' : Level
    A : Type ℓ

empty-α : ∀ (A : Type ℓ) -> sig emptySig A -> A
empty-α _ (x , _) = ⊥.rec x

emptyHomDegen : (𝔜 : struct ℓ' emptySig) -> structHom < A , empty-α A > 𝔜 ≃ (A -> 𝔜 .car)
emptyHomDegen _ = Σ-contractSnd λ _ -> isContrΠ⊥

module EmptyDef = F.Definition emptySig emptyEqSig emptySEq

empty-sat : ∀ (A : Type ℓ) -> < A , empty-α A > ⊨ emptySEq
empty-sat _ eqn ρ = ⊥.rec eqn

treeEmpty≃  : Tree emptySig A ≃ A
treeEmpty≃ = isoToEquiv (iso from leaf (λ _ -> refl) leaf∘from)
  where
  from : Tree emptySig A -> A
  from (leaf x) = x

  leaf∘from : retract from leaf
  leaf∘from (leaf x) = refl

treeDef : ∀ {ℓ ℓ'} -> EmptyDef.Free ℓ ℓ' 2
F.Definition.Free.F treeDef = Tree emptySig
F.Definition.Free.η treeDef = leaf
F.Definition.Free.α treeDef = empty-α (Tree emptySig _)
F.Definition.Free.sat treeDef = empty-sat (Tree emptySig _)
F.Definition.Free.isFree (treeDef {ℓ = ℓ}) {X = A} {𝔜 = 𝔜} H ϕ = lemma .snd
  where
  𝔗 : struct ℓ emptySig
  𝔗 = < Tree emptySig A , empty-α (Tree emptySig A) >

  lemma : structHom 𝔗 𝔜 ≃ (A -> 𝔜 .car)
  lemma =
    structHom 𝔗 𝔜 ≃⟨ emptyHomDegen 𝔜 ⟩
    (𝔗 .car -> 𝔜 .car) ≃⟨ equiv→ treeEmpty≃ (idEquiv (𝔜 .car)) ⟩
    (A -> 𝔜 .car) ■
    
anyDef : ∀ {ℓ ℓ'} -> EmptyDef.Free ℓ ℓ' 2
F.Definition.Free.F anyDef A = A
F.Definition.Free.η anyDef a = a
F.Definition.Free.α anyDef = empty-α _
F.Definition.Free.sat anyDef = empty-sat _
F.Definition.Free.isFree anyDef {𝔜 = 𝔜} _ _ = emptyHomDegen 𝔜 .snd
