{-# OPTIONS --cubical --safe --exact-split #-}

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
    car : Type n
    alg : sig σ car -> car
open struct public

module _ {f a x y : Level} {σ : Sig f a} (𝔛 : struct x σ) (𝔜 : struct y σ) where
  structIsHom : (h : 𝔛 .car -> 𝔜 .car) -> Type (ℓ-max f (ℓ-max a (ℓ-max x y)))
  structIsHom h =
    ((f : σ .symbol) -> (i : σ .arity f -> 𝔛 .car) -> 𝔜 .alg (f , h ∘ i) ≡ h (𝔛 .alg (f , i)))

  structHom : Type (ℓ-max f (ℓ-max a (ℓ-max x y)))
  structHom = Σ[ h ∈ (𝔛 .car -> 𝔜 .car) ] structIsHom h

  structHom≡ : (g h : structHom) -> isSet (𝔜 .car) -> g .fst ≡ h .fst -> g ≡ h
  structHom≡ (g-f , g-hom) (h-f , h-hom) isSetY =
    Σ≡Prop (\fun -> isPropΠ \f -> isPropΠ \o -> isSetY (𝔜 .alg (f , fun ∘ o)) (fun (𝔛 .alg (f , o))))

module _  {f a x : Level} {σ : Sig f a} (𝔛 : struct x σ) where
  idHom : structHom 𝔛 𝔛
  idHom = idfun _ , \f i -> refl

module _  {f a x y z : Level} {σ : Sig f a} (𝔛 : struct x σ) (𝔜 : struct y σ) (ℨ : struct z σ) where
  structHom∘ : (g : structHom 𝔜 ℨ) -> (h : structHom 𝔛 𝔜) -> structHom 𝔛 ℨ
  structHom∘ (g-f , g-hom) (h-f , h-hom) = g-f ∘ h-f , lemma-α
    where
    lemma-α : structIsHom 𝔛 ℨ (g-f ∘ h-f)
    lemma-α eqn i =
      ℨ .alg (eqn , g-f ∘ h-f ∘ i) ≡⟨ g-hom eqn (h-f ∘ i) ⟩
      g-f (𝔜 .alg (eqn , h-f ∘ i)) ≡⟨ cong g-f (h-hom eqn i) ⟩
      _ ∎
