{-# OPTIONS --cubical #-}

module Cubical.Structures.Str where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

open import Cubical.Structures.Sig

-- TODO: prove lemmas about its homotopy type
record struct {f a : Level} (n : Level) (σ : Sig f a) : Type (ℓ-max f (ℓ-max a (ℓ-suc n))) where
  constructor <_,_>
  field
    carrier : Type n
    algebra : sig σ carrier -> carrier
open struct public

module _  {f a x y : Level} {σ : Sig f a} (𝔛 : struct x σ) (𝔜 : struct y σ)  where
  structIsHom : (h : 𝔛 .carrier -> 𝔜 .carrier) -> Type (ℓ-max f (ℓ-max a (ℓ-max x y)))
  structIsHom h =
    ((f : σ .symbol) -> (i : σ .arity f -> 𝔛 .carrier) -> 𝔜 .algebra (f , h ∘ i) ≡ h (𝔛 .algebra (f , i)))

  structHom : Type (ℓ-max f (ℓ-max a (ℓ-max x y)))
  structHom = Σ[ h ∈ (𝔛 .carrier -> 𝔜 .carrier) ] structIsHom h

  structHom≡ : (g h : structHom) -> isSet (𝔜 .carrier) -> g .fst ≡ h .fst -> g ≡ h
  structHom≡ (g-f , g-hom) (h-f , h-hom) isSetY =
    Σ≡Prop (\fun -> isPropΠ \f -> isPropΠ \o -> isSetY (𝔜 .algebra (f , fun ∘ o)) (fun (𝔛 .algebra (f , o))))

module _  {f a x y z : Level} {σ : Sig f a} (𝔛 : struct x σ) (𝔜 : struct y σ) (ℨ : struct z σ) where
  structHom∘ : (g : structHom 𝔜 ℨ) -> (h : structHom 𝔛 𝔜) -> structHom 𝔛 ℨ
  structHom∘ (g-f , g-hom) (h-f , h-hom) = g-f ∘ h-f , lemma-α
    where
    lemma-α : structIsHom 𝔛 ℨ (g-f ∘ h-f)
    lemma-α eqn i =
      ℨ .algebra (eqn , g-f ∘ h-f ∘ i) ≡⟨ g-hom eqn (h-f ∘ i) ⟩
      g-f (𝔜 .algebra (eqn , h-f ∘ i)) ≡⟨ cong g-f (h-hom eqn i) ⟩
      _ ∎
