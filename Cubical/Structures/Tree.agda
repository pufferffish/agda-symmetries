{-# OPTIONS --cubical #-}

module Cubical.Structures.Tree where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Structures.Sig
open import Cubical.Structures.Str

module _ {f a n : Level} (σ : Sig f a) where
  data Tree (V : Type n) : Type (ℓ-max (ℓ-max f a) n) where
    leaf : V -> Tree V
    node : sig σ (Tree V) -> Tree V
  open Tree

module _ {f : Level} (σ : FinSig f) where
  FinTree : (k : ℕ) -> Type f
  FinTree k = Tree (finSig σ) (Fin k)

module _ {f a : Level} (σ : Sig f a) where
  algTr : ∀ {x} (X : Type x) -> struct (ℓ-max f (ℓ-max a x)) σ
  carrier (algTr X) = Tree σ X
  algebra (algTr X) = node

module _  {f a : Level} (σ : Sig f a) {x y} {X : Type x} (𝔜 : struct y σ) where
  private
    𝔛 : struct (ℓ-max f (ℓ-max a x)) σ
    𝔛 = algTr σ X

  sharp : (X -> 𝔜 .carrier) -> Tree σ X -> 𝔜 .carrier
  sharp ρ (leaf v) = ρ v
  sharp ρ (node (f , o)) = 𝔜 .algebra (f , sharp ρ ∘ o)

  eval : (X -> 𝔜 .carrier) -> structHom 𝔛 𝔜
  eval h = sharp h , λ _ _ -> refl

  sharp-eta : (g : structHom 𝔛 𝔜) -> (tr : Tree σ X) -> g .fst tr ≡ sharp (g .fst ∘ leaf) tr
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
