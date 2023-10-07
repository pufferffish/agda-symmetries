{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Arity where

import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Everything
open import Cubical.Data.Fin public renaming (Fin to Arity)
open import Cubical.Data.Fin.Recursive public using (rec)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Sigma

variable
  ℓ : Level
  A B : Type ℓ

private
  variable
    k : ℕ

ftwo : Arity (suc (suc (suc k)))
ftwo = fsuc fone

lookup : ∀ (xs : List A) -> Arity (length xs) -> A
lookup [] num = ⊥.rec (¬Fin0 num)
lookup (x ∷ xs) (zero , prf) = x
lookup (x ∷ xs) (suc num , prf) = lookup xs (num , pred-≤-pred prf)

tabulate : ∀ n -> (Arity n -> A) -> List A
tabulate zero ^a = []
tabulate (suc n) ^a = ^a fzero ∷ tabulate n (^a ∘ fsuc)

length-tabulate : ∀ n -> (^a : Arity n → A) -> length (tabulate n ^a) ≡ n
length-tabulate zero ^a = refl
length-tabulate (suc n) ^a = cong suc (length-tabulate n (^a ∘ fsuc))

tabulate-lookup : ∀ (xs : List A) -> tabulate (length xs) (lookup xs) ≡ xs
tabulate-lookup [] = refl
tabulate-lookup (x ∷ xs) =
   _ ≡⟨ cong (λ z -> x ∷ tabulate (length xs) z) (funExt λ _ -> cong (lookup xs) (Σ≡Prop (λ _ -> isProp≤) refl)) ⟩
   _ ≡⟨ cong (x ∷_) (tabulate-lookup xs) ⟩
   _ ∎
