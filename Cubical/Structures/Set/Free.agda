{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Free where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.FinData as F
open import Cubical.Data.List as L
open import Cubical.Data.List.FinData as F
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str
open import Cubical.Structures.Set.Tree
open import Cubical.Structures.Set.Eq

-- defines a free structure on a signature and equations
module Definition (σ : Sig ℓ-zero ℓ-zero) (τ : EqSig ℓ-zero ℓ-zero) (ε : seq σ τ) where
  record Free : Type (ℓ-suc ℓ-zero) where
    field
      F : (X : Type) -> Type
      α : {X : Type} -> sig σ (F X) -> F X
      sat : {X : Type} -> (F X , α) ⊨ ε
      η : {X : Type} -> X -> F X
      ext : {X : Type} {𝔜 : struct σ} {ϕ : 𝔜 ⊨ ε}
         -> (h : X -> 𝔜 .fst) -> structHom σ (F X , α) 𝔜
      ext-β : {X : Type} {𝔜 : struct σ} {ϕ : 𝔜 ⊨ ε} {h : X -> 𝔜 .fst}
         -> (ext {ϕ = ϕ} h .fst) ∘ η ≡ h
      ext-η : {X : Type} {𝔜 : struct σ} {ϕ : 𝔜 ⊨ ε} {H : structHom σ (F X , α) 𝔜}
         -> ext {ϕ = ϕ} (H .fst ∘ η) ≡ H

-- constructs a free structure on a signature and equations
-- TODO: generalise the universe levels!!
module Construction (σ : Sig ℓ-zero ℓ-zero) (τ : EqSig ℓ-zero ℓ-zero) (ε : seq σ τ) where

  data Free (X : Type) : Type ℓ-zero where
      η : X -> Free X
      α : sig σ (Free X) -> Free X
      sat : (Free X , α) ⊨ ε

  freeStruct : (X : Type) -> struct σ
  freeStruct X = Free X , α

  module _ (X : Type) (𝔜 : struct σ) (ϕ : 𝔜 ⊨ ε) where

    private
      Y = 𝔜 .fst
      β = 𝔜 .snd

    -- ext : (h : X -> Y) -> Free X -> Y
    -- ext h (η x) = h x
    -- ext h (α (f , o)) = β (f , (ext h ∘ o))
    -- ext h (sat e ρ i) = ϕ e (ext h ∘ ρ) {!!}

    -- module _  where
    --   postulate
    --     Fr : Type (ℓ-max (ℓ-max f a) n)
    --     Fα : sig σ Fr -> Fr
    --     Fs : sat σ τ ε (Fr , Fα)

    --   module _ (Y : Type (ℓ-max (ℓ-max f a) n)) (α : sig σ Y -> Y) where
    --     postulate
    --       Frec : sat σ τ ε (Y , α) -> Fr -> Y
    --       Fhom : (p : sat σ τ ε (Y , α)) -> walgIsH σ (Fr , Fα) (Y , α) (Frec p)
    --       Feta : (p : sat σ τ ε (Y , α)) (h : Fr -> Y) -> walgIsH σ (Fr , Fα) (Y , α) h -> Frec p ≡ h
