{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Tree where

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

module _ {f a n : Level} (σ : Sig f a) where
  data Tr (V : Type n) : Type (ℓ-max (ℓ-max f a) n) where
    leaf : V -> Tr V
    node : sig σ (Tr V) -> Tr V
  open Tr

module _ {f a : Level} (σ : Sig f a) where
  algTr : ∀ {x} (X : Type x) -> struct σ
  carrier (algTr X) = Tr σ X
  algebra (algTr X) = node

module _  {f a : Level} (σ : Sig f a) {x y} {X : Type x} {𝔜 : struct {f} {a} {y} σ} where
  𝔛 : struct σ
  𝔛 = algTr σ X

  sharp : (X -> 𝔜 .carrier) -> Tr σ X -> 𝔜 .carrier
  sharp ρ (leaf v) = ρ v
  sharp ρ (node (f , o)) = 𝔜 .algebra (f , sharp ρ ∘ o)

  eval : (X -> 𝔜 .carrier) -> structHom 𝔛 𝔜
  eval h = sharp h , λ _ _ -> refl

  sharp-eta : (g : structHom 𝔛 𝔜) -> (tr : Tr σ X) -> g .fst tr ≡ sharp (g .fst ∘ leaf) tr
  sharp-eta g (leaf x) = refl
  sharp-eta (g-f , g-hom) (node x) =
    g-f (node x) ≡⟨ sym (g-hom (x .fst) (x .snd)) ⟩
    𝔜 .algebra (x .fst , (λ y → g-f (x .snd y))) ≡⟨ cong (λ z → 𝔜 .algebra (x .fst , z)) (funExt λ y -> sharp-eta ((g-f , g-hom)) (x .snd y)) ⟩
    𝔜 .algebra (x .fst , (λ y → sharp (g-f ∘ leaf) (x .snd y)))
    ∎

  sharp-hom-eta : isSet (𝔜 .carrier) -> (g : structHom 𝔛 𝔜) -> g ≡ eval (g .fst ∘ leaf)
  sharp-hom-eta p g = structHom≡ 𝔛 𝔜 g (eval (g .fst ∘ leaf)) p (funExt (sharp-eta g))

  trEquiv : isSet (𝔜 .carrier) -> structHom 𝔛 𝔜 ≃ (X -> 𝔜 .carrier)
  trEquiv isSetY = isoToEquiv (iso (\g -> g .fst ∘ leaf) eval (\_ -> refl) (sym ∘ sharp-hom-eta isSetY))

  trIsEquiv : isSet (𝔜 .carrier) -> isEquiv (\g -> g .fst ∘ leaf)
  trIsEquiv = snd ∘ trEquiv
