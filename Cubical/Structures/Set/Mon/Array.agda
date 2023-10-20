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

open Iso

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ
    n m : ℕ

Array : Type ℓ -> Type ℓ
Array A = Σ[ n ∈ ℕ ] (Fin n -> A)

_⊕_ : Array A -> Array A -> Array A
(n , as) ⊕ (m , bs) = n + m , λ w -> ⊎.rec as bs (Fin+≅Fin⊎Fin n m .fun w)

e : Array A
e = 0 , ⊥.rec ∘ ¬Fin0

⊕-unitl : ∀ {ℓ} {A : Type ℓ} -> (xs : Array A) -> e ⊕ xs ≡ xs
⊕-unitl (n , xs) = ΣPathP (refl , funExt lemma)
  where
  lemma : (x : Fin (fst (e ⊕ (n , xs)))) -> snd (e ⊕ (n , xs)) x ≡ xs x
  lemma (n , p) with n ≤? 0
  ... | inl q = ⊥.rec (¬-<-zero q)
  ... | inr q = refl

⊕-unitr : ∀ {ℓ} {A : Type ℓ} -> (xs : Array A) -> xs ⊕ e ≡ xs
⊕-unitr {A = A} (n , xs) = ΣPathP (+-zero n , toPathP (funExt lemma))
  where
  lemma : _
  lemma (m , p) with m ≤? n
  ... | inl q =
    transport (λ i -> A) (xs (m , q)) ≡⟨ sym (transport-filler refl (xs (m , q))) ⟩
    xs (m , q) ≡⟨ cong xs (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
    xs (m , p) ∎
  ... | inr q = ⊥.rec ((<-asym p) q)

∸-+-assoc : ∀ m n o → m ∸ n ∸ o ≡ m ∸ (n + o)
∸-+-assoc m       n       zero    = cong (m ∸_) (sym (+-zero n))
∸-+-assoc zero    zero    (suc o) = refl
∸-+-assoc zero    (suc n) (suc o) = refl
∸-+-assoc (suc m) zero    (suc o) = refl
∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc m n (suc o)

⊕-assocr : ∀ {ℓ} {A : Type ℓ} (m n o : Array A) -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
⊕-assocr {A = A} (n , as) (m , bs) (o , cs) = ΣPathP (sym (+-assoc n m o) , toPathP (funExt lemma))
  where
  lemma : _
  lemma (w , p) with w ≤? (n + m)
  lemma (w , p) | inl q with w ≤? n
  lemma (w , p) | inl q | inl r =
    sym (transport-filler refl (as (w , r)))
  lemma (w , p) | inl q | inr r with (w ∸ n) ≤? m
  lemma (w , p) | inl q | inr r | inl s =
    _ ≡⟨ sym (transport-filler refl _) ⟩
    bs (w ∸ n , _) ≡⟨ cong bs (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
    bs (w ∸ n , s) ∎
  lemma (w , p) | inl q | inr r | inr s =
    ⊥.rec (<-asym q t)
    where
    t : n + m ≤ w
    t = subst (n + m ≤_) (+-comm n (w ∸ n) ∙ ≤-∸-+-cancel r) (≤-k+ s)
  lemma (w , p) | inr q with w ≤? n
  lemma (w , p) | inr q | inl r =
    ⊥.rec (¬m+n<m (≤<-trans q r))
  lemma (w , p) | inr q | inr r with (w ∸ n) ≤? m
  lemma (w , p) | inr q | inr r | inl s =
    ⊥.rec (<-asym t q)
    where
    t : w < n + m
    t = subst2 _<_ (≤-∸-+-cancel r) (+-comm m n) (≤-+k s)
  lemma (w , p) | inr q | inr r | inr s =
    _ ≡⟨ sym (transport-filler refl _) ⟩
    cs (w ∸ (n + m) , _) ≡⟨ cong cs (Σ≡Prop (λ _ -> isProp≤) (sym (∸-+-assoc w n m))) ⟩
    cs (w ∸ n ∸ m , _) ∎