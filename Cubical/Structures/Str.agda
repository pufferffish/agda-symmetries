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
open import Cubical.Structures.Arity

-- TODO: prove lemmas about its homotopy type
record struct {f : Level} (n : Level) (σ : Sig f) : Type (ℓ-max f (ℓ-suc n)) where
  constructor <_,_>
  field
    carrier : Type n
    algebra : sig σ carrier -> carrier
open struct public

module _  {f x y : Level} {σ : Sig f} (𝔛 : struct x σ) (𝔜 : struct y σ)  where
  structIsHom : (h : 𝔛 .carrier -> 𝔜 .carrier) -> Type (ℓ-max f (ℓ-max x y))
  structIsHom h =
    ((f : σ .symbol) -> (i : Operands (σ .arity f) (𝔛 .carrier)) -> 𝔜 .algebra (f , omap h i) ≡ h (𝔛 .algebra (f , i)))

  structHom : Type (ℓ-max f (ℓ-max x y))
  structHom = Σ[ h ∈ (𝔛 .carrier -> 𝔜 .carrier) ] structIsHom h

  structHom≡ : (g h : structHom) -> isSet (𝔜 .carrier) -> g .fst ≡ h .fst -> g ≡ h
  structHom≡ (g-f , g-hom) (h-f , h-hom) isSetY =
    Σ≡Prop (\fun -> isPropΠ \f -> isPropΠ \o -> isSetY (𝔜 .algebra (f , omap fun o)) (fun (𝔛 .algebra (f , o))))
