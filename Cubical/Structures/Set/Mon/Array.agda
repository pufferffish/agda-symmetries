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

open import Cubical.Structures.Inspect

open Iso

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ
    n m : ℕ

Array : Type ℓ -> Type ℓ
Array A = Σ[ n ∈ ℕ ] (Fin n -> A)

finSplitAux : ∀ m n k -> k < m + n -> (k < m) ⊎ (m ≤ k) -> Fin m ⊎ Fin n
finSplitAux m n k k<m+n (inl k<m) = inl (k , k<m)
finSplitAux m n k k<m+n (inr k≥m) = inr (k ∸ m , ∸-<-lemma m n k k<m+n k≥m)

finSplit : ∀ m n -> Fin (m + n) -> Fin m ⊎ Fin n
finSplit m n (k , k<m+n) = finSplitAux m n k k<m+n (k ≤? m)

combine : ∀ n m -> (Fin n -> A) -> (Fin m -> A) -> (Fin (n + m) -> A)
combine n m as bs w = ⊎.rec as bs (finSplit n m w)

_⊕_ : Array A -> Array A -> Array A
(n , as) ⊕ (m , bs) = n + m , combine n m as bs

e : Array A
e = 0 , ⊥.rec ∘ ¬Fin0

e-eta : ∀ (xs ys : Array A) -> xs .fst ≡ 0 -> ys .fst ≡ 0 -> xs ≡ ys
e-eta (n , xs) (m , ys) p q = ΣPathP (p ∙ sym q , toPathP (funExt lemma))
  where
  lemma : _
  lemma x = ⊥.rec (¬Fin0 (subst Fin q x))

η : A -> Array A
η x = 1 , λ _ -> x

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
⊕-assocr (n , as) (m , bs) (o , cs) = ΣPathP (sym (+-assoc n m o) , toPathP (funExt lemma))
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

cons : A -> (Fin n -> A) -> (Fin (suc n) -> A)
cons x xs (zero , p) = x
cons x xs (suc n , p) = xs (n , pred-≤-pred p)

_∷_ : A -> Array A -> Array A
x ∷ (n , xs) = (suc n) , cons x xs

uncons : (Fin (suc n) -> A) -> A × (Fin n -> A)
uncons xs = xs fzero , xs ∘ fsuc

η+fsuc : ∀ {n} (xs : Fin (suc n) -> A) -> η (xs fzero) ⊕ (n , xs ∘ fsuc) ≡ (suc n , xs)
η+fsuc {n = n} xs = ΣPathP (refl , funExt lemma)
  where
  lemma : _
  lemma (zero , p) = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)
  lemma (suc m , p) with oldInspect (suc m ≤? 1)
  ... | inl q with-≡ r = ⊥.rec (¬-<-zero (pred-≤-pred q))
  ... | inr q with-≡ r =
    _ ≡⟨ cong (λ z -> ⊎.rec _ _ (finSplitAux 1 n (suc m) p z)) r ⟩
    _ ≡⟨ cong xs (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
    _ ∎

¬n<m<suc-n : ∀ {n m} -> n < m -> m < suc n -> ⊥.⊥
¬n<m<suc-n {n} {m} (x , p) (y , q) = znots lemma-β
  where
  lemma-α : suc n ≡ (y + suc x) + suc n
  lemma-α =
    suc n ≡⟨ sym q ⟩
    y + suc m ≡⟨ cong (λ z -> y + suc z) (sym p) ⟩
    y + (suc x + suc n) ≡⟨ +-assoc y (suc x) (suc n) ⟩
    (y + suc x) + suc n ∎
  lemma-β : 0 ≡ suc (y + x)
  lemma-β = (sym (n∸n (suc n))) ∙ cong (_∸ suc n) lemma-α ∙ +∸ (y + suc x) (suc n) ∙ +-suc y x

⊕-split : ∀ n m (xs : Fin (suc n) -> A) (ys : Fin m -> A) ->
  (n + m , (λ w -> combine (suc n) m xs ys (fsuc w)))
  ≡ ((n , (λ w -> xs (fsuc w))) ⊕ (m , ys))
⊕-split n m xs ys = ΣPathP (refl , funExt lemma)
  where
  lemma : _
  lemma (o , p) with suc o ≤? suc n
  lemma (o , p) | inl q with o ≤? n
  lemma (o , p) | inl q | inl r = {!   !}
  lemma (o , p) | inl q | inr r = ⊥.rec (<-asym (pred-≤-pred q) r)
  lemma (o , p) | inr q with o ≤? n
  lemma (o , p) | inr q | inl r = ⊥.rec (¬n<m<suc-n r q)
  lemma (o , p) | inr q | inr r = {!   !}

array-α : sig M.MonSig (Array A) -> Array A
array-α (M.`e , i) = e
array-α (M.`⊕ , i) = i fzero ⊕ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where  
  module 𝔜 = M.MonSEq 𝔜 𝔜-monoid

  𝔄 : M.MonStruct
  𝔄 = < Array A , array-α >

  module _ (f : A -> 𝔜 .car) where
    ♯' : (n : ℕ) -> (Fin n -> A) -> 𝔜 .car
    ♯' zero    _  = 𝔜.e
    ♯' (suc n) xs = f (xs fzero) 𝔜.⊕ ♯' n (xs ∘ fsuc)

    _♯ : Array A -> 𝔜 .car
    (n , xs) ♯ = ♯' n xs -- to aid termination checker

    ♯-η∘ : ∀ (xs : Fin (suc n) -> A)
      -> (η (xs fzero) ♯) 𝔜.⊕ ((n , xs ∘ fsuc) ♯)
      ≡  ((η (xs fzero) ⊕ (n , xs ∘ fsuc)) ♯)
    ♯-η∘ xs = {!   !}

    ♯-++' : ∀ n xs m ys -> ((n , xs) ⊕ (m , ys)) ♯ ≡ ((n , xs) ♯) 𝔜.⊕ ((m , ys) ♯)
    ♯-++' zero xs m ys =
      ((zero , xs) ⊕ (m , ys)) ♯ ≡⟨ cong (λ z -> (z ⊕ (m , ys)) ♯) (e-eta (zero , xs) e refl refl) ⟩
      (e ⊕ (m , ys)) ♯ ≡⟨ cong _♯ (⊕-unitl (m , ys)) ⟩
      (m , ys) ♯ ≡⟨ sym (𝔜.unitl _) ⟩
      𝔜.e 𝔜.⊕ ((m , ys) ♯) ∎
    ♯-++' (suc n) xs m ys =
        f (xs fzero) 𝔜.⊕ ((n + m , _) ♯)
      ≡⟨ cong (λ z -> f (xs fzero) 𝔜.⊕ (z ♯)) (⊕-split n m xs ys) ⟩
        f (xs fzero) 𝔜.⊕ (((n , xs ∘ fsuc) ⊕ (m , ys)) ♯)
      ≡⟨ cong (f (xs fzero) 𝔜.⊕_) (♯-++' n _ m _) ⟩
        f (xs fzero) 𝔜.⊕ ((n , xs ∘ fsuc) ♯) 𝔜.⊕ ((m , ys) ♯)
      ≡⟨ sym (𝔜.assocr _ _ _) ⟩
        (f (xs fzero) 𝔜.⊕ ((n , xs ∘ fsuc) ♯)) 𝔜.⊕ ((m , ys) ♯)
      ≡⟨ cong (λ z -> (z 𝔜.⊕ ((n , xs ∘ fsuc) ♯)) 𝔜.⊕ ((m , ys) ♯) ) (sym (𝔜.unitr _)) ⟩
        ((η (xs fzero) ♯) 𝔜.⊕ ((n , xs ∘ fsuc) ♯)) 𝔜.⊕ ((m , ys) ♯)
      ≡⟨ cong (𝔜._⊕ ((m , ys) ♯)) (♯-η∘ xs) ⟩ -- cannot reuse ♯-++' because of termination checker
        ((η (xs fzero) ⊕ (n , xs ∘ fsuc)) ♯) 𝔜.⊕ ((m , ys) ♯)
      ≡⟨ cong (λ z -> (z ♯) 𝔜.⊕ ((m , ys) ♯)) (η+fsuc xs) ⟩
        ((suc n , xs) ♯) 𝔜.⊕ ((m , ys) ♯) ∎

    ♯-++ : ∀ xs ys -> (xs ⊕ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
    ♯-++ (n , xs) (m , ys) = ♯-++' n xs m ys

    ♯-isMonHom : structHom 𝔄 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ ∙ sym (♯-++ (i fzero) (i fone))

 