{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Array where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum as ⊎
open import Cubical.Induction.WellFounded
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ
    n m : ℕ

Array : Type ℓ -> Type ℓ
Array A = Σ[ n ∈ ℕ ] (Fin n -> A)

cons : A -> (Fin n -> A) -> (Fin (suc n) -> A)
cons x xs (zero , p) = x
cons x xs (suc n , p) = xs (n , pred-≤-pred p)

uncons : (Fin (suc n) -> A) -> A × (Fin n -> A)
uncons xs = xs fzero , xs ∘ fsuc

cons∘uncons : (xs : Fin (suc n) -> A) -> uncurry cons (uncons xs) ≡ xs
cons∘uncons xs = funExt lemma
  where
  lemma : _
  lemma (zero , p) = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)
  lemma (suc n , p) = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)

uncons∘cons : (x : A) -> (xs : Fin (suc n) -> A) -> uncons (cons x xs) ≡ (x , xs)
uncons∘cons x xs = cong (x ,_) (funExt λ _ -> cong xs (Σ≡Prop (λ _ -> isProp≤) refl))

_∷_ : A -> Array A -> Array A
x ∷ (n , xs) = (suc n) , cons x xs

⊕-compute : (n : ℕ) -> (Fin n -> A) -> Array A -> Array A
⊕-compute zero as bs = bs
⊕-compute (suc n) as bs = let (head , tail) = uncons as in head ∷ ⊕-compute n tail bs

_⊕_ : Array A -> Array A -> Array A
(n , as) ⊕ bs = ⊕-compute n as bs -- to help with termination checking

{-# DISPLAY ⊕-compute (n , as) bs = (n , as) ⊕ bs #-}

e : Array A
e = 0 , ⊥.rec ∘ ¬Fin0

⊕-unitl : (xs : Array A) -> e ⊕ xs ≡ xs
⊕-unitl (n , xs) = ΣPathP (refl , funExt λ _ -> refl)

-- ⊕-unitr'' : (f : Fin n -> A) -> (⊕-compute n f e) .snd ≡ {!   !}
-- ⊕-unitr'' n f = {!   !}

⊕-unitr' : (n : ℕ) -> (xs : Fin n -> A) -> (n , xs) ⊕ e ≡ (n , xs)
⊕-unitr' zero xs = ΣPathP (refl , funExt λ (_ , p) -> ⊥.rec (¬-<-zero p))
⊕-unitr' (suc n) xs =
  let (indL , indI) = PathPΣ (⊕-unitr' n (xs ∘ fsuc))
  in ΣPathP (cong suc indL , λ i x -> {!   !})

-- ⊕-unitr : (xs : Array A) -> xs ⊕ e ≡ xs
-- ⊕-unitr (zero , xs) = ΣPathP (refl , funExt λ (_ , p) -> ⊥.rec (¬-<-zero p))
-- ⊕-unitr (suc n , xs) = 
--   let (indL , indI) = PathPΣ (⊕-unitr (n , xs ∘ fsuc))
--   in ΣPathP (cong suc indL , {!   !}) 