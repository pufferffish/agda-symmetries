{-# OPTIONS --cubical #-}

module Cubical.Structures.Sig where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.InfNat
open import Cubical.Data.Fin
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Cubical.Structures.Arity
open import Agda.Primitive

record Sig (f : Level) : Type (ℓ-suc f) where
  field
    symbol : Type f
    arity : symbol -> ℕ+∞
open Sig public

FinSig : (f : Level) -> Type (ℓ-suc f)
FinSig f = Σ (Type f) \sym -> sym -> ℕ

finSig : {f : Level} -> FinSig f -> Sig f
symbol (finSig σ) = σ .fst
arity (finSig σ) = fin ∘ σ .snd

-- signature functor
module _ {f n : Level} (σ : Sig f) where
  sig : Type n -> Type (ℓ-max f n)
  sig X = Σ (σ .symbol) \f -> Operands (σ .arity f) X

  sig≡ : {X : Type n} (f : σ .symbol) {i j : Operands (σ .arity f) X}
      -> (i ≡ j)
      -> Path (sig X) (f , i) (f , j)
  sig≡ f H = ΣPathP (refl , H)

  sigF : {X Y : Type n} -> (X -> Y) -> sig X -> sig Y
  sigF h (f , i) = f , omap h i
  