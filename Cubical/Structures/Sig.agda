{-# OPTIONS --cubical #-}

module Cubical.Structures.Sig where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

record Sig (f a : Level) : Type ((ℓ-suc f) ⊔ (ℓ-suc a)) where
  field
    symbol : Type f
    arity : symbol -> Type a
open Sig public

FinSig : (f : Level) -> Type (ℓ-suc f)
FinSig f = Σ (Type f) \sym -> sym -> ℕ

finSig : {f : Level} -> FinSig f -> Sig f ℓ-zero
symbol (finSig σ) = σ .fst
arity (finSig σ) = Fin ∘ σ .snd

emptySig : Sig ℓ-zero ℓ-zero
symbol emptySig = ⊥.⊥
arity emptySig = ⊥.rec

sumSig : {f a g b : Level} -> Sig f a -> Sig g b -> Sig (ℓ-max f g) (ℓ-max a b)
symbol (sumSig σ τ) = symbol σ ⊎ symbol τ
arity (sumSig {b = b} σ τ) (inl x) = Lift {j = b} ((arity σ) x)
arity (sumSig {a = a} σ τ) (inr x) = Lift {j = a} ((arity τ) x)

-- signature functor
module _ {f a n : Level} (σ : Sig f a) where
  sig : Type n -> Type (ℓ-max f (ℓ-max a n))
  sig X = Σ (σ .symbol) \f -> σ .arity f -> X

  sig≡ : {X : Type n} (f : σ .symbol) {i j : σ .arity f -> X}
      -> ((a : σ .arity f) -> i a ≡ j a)
      -> Path (sig X) (f , i) (f , j)
  sig≡ f H = ΣPathP (refl , funExt H)

  sigF : {X Y : Type n} -> (X -> Y) -> sig X -> sig Y
  sigF h (f , i) = f , h ∘ i

module _ {f n : Level} (σ : FinSig f) where
  sigFin : (X : Type n) -> Type (ℓ-max f n)
  sigFin X = sig (finSig σ) X

  sigFin≡ : {X : Type n} (f : σ .fst) {i j : finSig σ .arity f -> X}
         -> ((a : finSig σ .arity f) -> i a ≡ j a)
         -> Path (sigFin X) (f , i) (f , j)
  sigFin≡ = sig≡ (finSig σ)
