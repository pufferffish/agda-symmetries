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

private
  variable
    ℓ : Level
    A B : Type ℓ
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

arity-n≡m : ∀ {n m} -> (a : Arity n) -> (b : Arity m) -> (p : n ≡ m) -> a .fst ≡ b .fst -> PathP (λ i -> Arity (p i)) a b
arity-n≡m (v , a) (w , b) p q = ΣPathP (q , toPathP (isProp≤ _ _))

lookup-tabulate : ∀ n (^a : Arity n -> A) -> PathP (λ i -> (Arity (length-tabulate n ^a i) -> A)) (lookup (tabulate n ^a)) ^a
lookup-tabulate zero ^a = funExt (⊥.rec ∘ ¬Fin0)
lookup-tabulate (suc n) ^a = toPathP (funExt lemma) -- i (zero , p) =  ^a (0 , toPathP {A = λ j -> 0 < suc (length-tabulate n (^a ∘ fsuc) (~ j))} {!   !} i) -- toPathP (sym (transport-filler _ _) ∙ cong ^a (Σ≡Prop (λ _ -> isProp≤) refl)) i -- suc-≤-suc (zero-≤ {n = n}) toPathP {x = suc-≤-suc (zero-≤ {n = n})} {!   !} i
  where
  lemma : _
  lemma (zero , p) = sym (transport-filler _ _) ∙ cong ^a (Σ≡Prop (λ _ -> isProp≤) refl)
  -- TODO: Cleanup this mess
  lemma (suc w , p) =
    _ ≡⟨ sym (transport-filler _ _) ⟩
    _ ≡⟨ congP (λ i f -> f (arity-n≡m (w ,
       pred-≤-pred
       (transp
        (λ i → suc w < suc (length-tabulate n (λ x → ^a (fsuc x)) (~ i)))
        i0 p)) (w , pred-≤-pred p) (length-tabulate n (^a ∘ fsuc)) refl i)) (lookup-tabulate n (^a ∘ fsuc)) ⟩
    _ ≡⟨ cong ^a (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
    _ ∎

lookup2≡i : ∀ (i : Arity 2 -> A) -> lookup (i fzero ∷ i fone ∷ []) ≡ i
lookup2≡i i = funExt lemma
  where
  lemma : _
  lemma (zero , p) = cong i (Σ≡Prop (λ _ -> isProp≤) refl)
  lemma (suc zero , p) = cong i (Σ≡Prop (λ _ -> isProp≤) refl)
  lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

◼ : Arity 0 -> A
◼ = ⊥.rec ∘ ¬Fin0

infixr 30 _▸_

_▸_ : ∀ {n} -> A -> (Arity n -> A) -> Arity (suc n) -> A
_▸_ {n = zero} x f i = x
_▸_ {n = suc n} x f i = lookup (x ∷ tabulate (suc n) f) (subst Arity (congS (suc ∘ suc) (sym (length-tabulate n (f ∘ fsuc)))) i)

⟪⟫ : Arity 0 -> A
⟪⟫ = lookup []

⟪_⟫ : (a : A) -> Arity 1 -> A
⟪ a ⟫ = lookup [ a ]

⟪_⨾_⟫ : (a b : A) -> Arity 2 -> A
⟪ a ⨾ b ⟫ = lookup (a ∷ b ∷ [])

⟪_⨾_⨾_⟫ : (a b c : A) -> Arity 3 -> A
⟪ a ⨾ b ⨾ c ⟫ = lookup (a ∷ b ∷ c ∷ [])
 