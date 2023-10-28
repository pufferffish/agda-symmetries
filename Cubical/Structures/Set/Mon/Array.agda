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
    A B C : Type ℓ
    n m : ℕ

Array : Type ℓ -> Type ℓ
Array A = Σ[ n ∈ ℕ ] (Fin n -> A)

isSetArray : isSet A -> isSet (Array A)
isSetArray isSetA = isOfHLevelΣ 2 isSetℕ λ _ -> isOfHLevelΠ 2 λ _ -> isSetA

-- TODO: Prove tptLemma using transp, not J
tptLemma : ∀ {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (P : A -> Type ℓ'') {a b : A} (p : a ≡ b) (f : P a -> B) (k : P b)
        -> transport (\i -> P (p i) -> B) f k ≡ f (transport (\i -> P (p (~ i))) k)
tptLemma A B P {a} =
  J (\b p -> (f : P a -> B) (k : P b)
        -> transport (\i -> P (p i) -> B) f k ≡ f (transport (\i -> P (p (~ i))) k))
    \f k -> cong (transp (\i -> B) i0 ∘ f) (transportRefl k)
         ∙ transportRefl (f k)
         ∙ cong f (sym (transportRefl k))

Array≡ : ∀ {ℓ} {A : Type ℓ} {n m} {f : Fin n -> A} {g : Fin m -> A}
      -> (n=m : n ≡ m)
      -> (∀ (k : ℕ) (k<m : k < m) -> f (k , subst (k <_) (sym n=m) k<m) ≡ g (k , k<m))
      -> Path (Array A) (n , f) (m , g)
Array≡ {A = A} {n = n} {m} {f} {g} p h = ΣPathP (p , toPathP (funExt lemma))
  where
    lemma : (k : Fin m) -> transport (\i -> Fin (p i) -> A) f k ≡ g k
    lemma k = tptLemma ℕ A Fin p f k ∙ h (k .fst) (k .snd)

ℕ≡→Fin̄≅ : ∀ {n m} -> n ≡ m -> Fin n ≃ Fin m
ℕ≡→Fin̄≅ {n = n} {m = m} p = univalence .fst (cong Fin p)

⊎-inl-beta : (B : Type ℓ) (f : A -> C) (g : B -> C) -> (a : A) -> ⊎.rec f g (inl a) ≡ f a
⊎-inl-beta B f g a = refl

⊎-inr-beta : (A : Type ℓ) (f : A -> C) (g : B -> C) -> (b : B) -> ⊎.rec f g (inr b) ≡ g b
⊎-inr-beta A f g b = refl

⊎-eta : {f : A -> C} {g : B -> C} -> (h : A ⊎ B -> C) (h1 : f ≡ h ∘ inl) (h2 : g ≡ h ∘ inr) -> ⊎.rec f g ≡ h
⊎-eta h h1 h2 i (inl a) = h1 i a
⊎-eta h h1 h2 i (inr b) = h2 i b

∸-<-lemma⁻ : (m n o : ℕ) -> m ≤ o -> o ∸ m < n -> o < m + n
∸-<-lemma⁻ zero n o m≤o o∸m<n = o∸m<n
∸-<-lemma⁻ (suc m) n zero m≤o o∸m<n = suc-≤-suc zero-≤
∸-<-lemma⁻ (suc m) n (suc o) m≤o o∸m<n = suc-≤-suc (∸-<-lemma⁻ m n o (pred-≤-pred m≤o) o∸m<n)

finSplitAux : ∀ m n k -> k < m + n -> (k < m) ⊎ (m ≤ k) -> Fin m ⊎ Fin n
finSplitAux m n k k<m+n (inl k<m) = inl (k , k<m)
finSplitAux m n k k<m+n (inr k≥m) = inr (k ∸ m , ∸-<-lemma m n k k<m+n k≥m)

finSplit : ∀ m n -> Fin (m + n) -> Fin m ⊎ Fin n
finSplit m n (k , k<m+n) = finSplitAux m n k k<m+n (k ≤? m)

finSplit-beta-inl-aux : ∀ {m n} (k : ℕ) (k<m : k < m) -> finSplit m n (k , o<m→o<m+n m n k k<m) ≡ inl (k , k<m)
finSplit-beta-inl-aux {m} {n} k k<m! with k ≤? m
... | inl k<m = congS (\p -> inl (k , p)) (isProp≤ k<m k<m!)
... | inr m≤k = ⊥.rec (¬-<-and-≥ k<m! m≤k)

finSplit-beta-inl : ∀ {m n} (k : ℕ) (k<m : k < m) (k<m+n : k < m + n) -> finSplit m n (k , k<m+n) ≡ inl (k , k<m)
finSplit-beta-inl {m} {n} k k<m k<m+n =
  finSplit m n (k , k<m+n) ≡⟨ congS (\ϕ -> finSplit m n (k , ϕ)) (isProp≤ k<m+n (o<m→o<m+n m n k k<m)) ⟩
  finSplit m n (k , o<m→o<m+n m n k k<m) ≡⟨ finSplit-beta-inl-aux k k<m ⟩
  inl (k , k<m) ∎

finSplit-beta-inr-aux : ∀ {m n} (k : ℕ) (m≤k : m ≤ k) (k∸m<n : k ∸ m < n) -> finSplit m n (k , ∸-<-lemma⁻ m n k m≤k k∸m<n) ≡ inr (k ∸ m , k∸m<n)
finSplit-beta-inr-aux {m} {n} k m≤k! k∸m<n with k ≤? m
... | inl k<m = ⊥.rec (¬-<-and-≥ k<m m≤k!)
... | inr m≤k = congS (\p -> inr (k ∸ m , p)) (isProp≤ (∸-<-lemma m n k (∸-<-lemma⁻ m n k m≤k! k∸m<n) m≤k) k∸m<n)

n+m∸n=m : ∀ n m -> n + m ∸ n ≡ m
n+m∸n=m n m = congS (_∸ n) (+-comm n m) ∙ m+n∸n=m n m

finSplit-beta-inr : ∀ {m n} (k : ℕ) (k<m+n : k < m + n) (m≤k : m ≤ k) (k∸m<n : k ∸ m < n) -> finSplit m n (k , k<m+n) ≡ inr (k ∸ m , k∸m<n)
finSplit-beta-inr {m} {n} k k<m+n m≤k k∸m<n =
    finSplit m n (k , k<m+n)
  ≡⟨ congS (\ϕ -> finSplit m n (k , ϕ)) (isProp≤ k<m+n (∸-<-lemma⁻ m n k m≤k k∸m<n)) ⟩
    finSplit m n (k , ∸-<-lemma⁻ m n k m≤k k∸m<n)
  ≡⟨ finSplit-beta-inr-aux k m≤k k∸m<n ⟩
    inr (k ∸ m , k∸m<n)
  ∎

finSplit-beta-inr-+ : ∀ {m n} (k : ℕ) (k<n : k < n) -> finSplit m n (m + k , <-k+ {k = m} k<n) ≡ inr (k , k<n)
finSplit-beta-inr-+ {m} {n} k k<n =
    finSplit m n (m + k , <-k+ {k = m} k<n)
  ≡⟨ finSplit-beta-inr (m + k) (<-k+ k<n) ≤SumLeft (subst (_< n) (sym (n+m∸n=m m k)) k<n) ⟩
    inr (m + k ∸ m , subst (_< n) (sym (n+m∸n=m m k)) k<n)
  ≡⟨ congS inr (Σ≡Prop (\_ -> isProp≤) (n+m∸n=m m k)) ⟩
     inr (k , k<n)
  ∎

finCombine-inl : Fin m -> Fin (m + n)
finCombine-inl {m = m} {n = n} (k , k<m) = k , o<m→o<m+n m n k k<m

finCombine-inr : Fin n -> Fin (m + n)
finCombine-inr {n = n} {m = m} (k , k<n) = m + k , <-k+ k<n

finCombine : ∀ m n -> Fin m ⊎ Fin n -> Fin (m + n)
finCombine m n = ⊎.rec finCombine-inl finCombine-inr

finSplit∘finCombine : ∀ m n x -> (finSplit m n ∘ finCombine m n) x ≡ x
finSplit∘finCombine m n =
  ⊎.elim (\(k , k<m) ->
              finSplit m n (finCombine m n (inl (k , k<m)))
         ≡⟨ congS (finSplit m n) (⊎-inl-beta (Fin n) finCombine-inl finCombine-inr (k , k<m)) ⟩
              finSplit m n (k , o<m→o<m+n m n k k<m)
         ≡⟨ finSplit-beta-inl k k<m (o<m→o<m+n m n k k<m) ⟩
              inl (k , k<m)
         ∎)
         (\(k , k<n) ->
              finSplit m n (finCombine m n (inr (k , k<n)))
         ≡⟨ congS (finSplit m n) (⊎-inr-beta (Fin m) finCombine-inl finCombine-inr (k , k<n)) ⟩
              finSplit m n (m + k , <-k+ k<n)
         ≡⟨ finSplit-beta-inr-+ k k<n ⟩
              inr (k , k<n)
         ∎)

finCombine∘finSplit : ∀ m n x -> (finCombine m n ∘ finSplit m n) x ≡ x
finCombine∘finSplit m n (k , k<m+n) =
  ⊎.rec (\k<m ->
              finCombine m n (finSplit m n (k , k<m+n))
        ≡⟨ congS (finCombine m n) (finSplit-beta-inl k k<m k<m+n) ⟩
              finCombine m n (inl (k , k<m))
        ≡⟨ ⊎-inl-beta (Fin n) finCombine-inl finCombine-inr (k , k<m) ⟩
              (k , o<m→o<m+n m n k k<m)
        ≡⟨ Σ≡Prop (\_ -> isProp≤) refl ⟩
              (k , k<m+n)
        ∎)
        (\m≤k ->
              finCombine m n (finSplit m n (k , k<m+n))
        ≡⟨ congS (finCombine m n) (finSplit-beta-inr k k<m+n m≤k (∸-<-lemma m n k k<m+n m≤k)) ⟩
              finCombine m n (inr (k ∸ m , ∸-<-lemma m n k k<m+n m≤k))
        ≡⟨ ⊎-inr-beta (Fin m) finCombine-inl finCombine-inr (k ∸ m , ∸-<-lemma m n k k<m+n m≤k) ⟩
              finCombine-inr (k ∸ m , ∸-<-lemma m n k k<m+n m≤k)
        ≡⟨ Σ≡Prop (\_ -> isProp≤) (≤-∸-k m≤k ∙ n+m∸n=m m k) ⟩
              (k , k<m+n)
        ∎)
        (k ≤? m)

Fin≅Fin+Fin : ∀ m n -> Fin (m + n) ≃ (Fin m ⊎ Fin n)
Fin≅Fin+Fin m n = isoToEquiv (iso (finSplit m n) (finCombine m n) (finSplit∘finCombine m n) (finCombine∘finSplit m n))

combine : ∀ n m -> (Fin n -> A) -> (Fin m -> A) -> (Fin (n + m) -> A)
combine n m as bs w = ⊎.rec as bs (finSplit n m w)

_⊕_ : Array A -> Array A -> Array A
(n , as) ⊕ (m , bs) = n + m , combine n m as bs

e-fun : Fin 0 -> A
e-fun = ⊥.rec ∘ ¬Fin0

e : Array A
e = 0 , e-fun

e-eta : ∀ (xs ys : Array A) -> xs .fst ≡ 0 -> ys .fst ≡ 0 -> xs ≡ ys
e-eta (n , xs) (m , ys) p q = ΣPathP (p ∙ sym q , toPathP (funExt lemma))
  where
  lemma : _
  lemma x = ⊥.rec (¬Fin0 (subst Fin q x))

η : A -> Array A
η x = 1 , λ _ -> x

zero-+ : ∀ m → 0 + m ≡ m
zero-+ m = refl

⊕-unitl : ∀ {ℓ} {A : Type ℓ} -> (xs : Array A) -> e ⊕ xs ≡ xs
⊕-unitl (n , f) = Array≡ (zero-+ n) \k k<n ->
    ⊎.rec e-fun f (finSplit 0 n (k , subst (k <_) (sym (zero-+ n)) k<n))
  ≡⟨ congS (⊎.rec e-fun f) (finSplit-beta-inr k (subst (k <_) (sym (zero-+ n)) k<n) zero-≤ k<n) ⟩
    ⊎.rec e-fun f (inr (k , k<n))
  ≡⟨ ⊎-inr-beta (Fin 0) e-fun f (k , k<n) ⟩
    f (k , k<n)
  ∎

⊕-unitr : ∀ {ℓ} {A : Type ℓ} -> (xs : Array A) -> xs ⊕ e ≡ xs
⊕-unitr (n , f) = Array≡ (+-zero n) \k k<n ->
    ⊎.rec f e-fun (finSplit n 0 (k , subst (k <_) (sym (+-zero n)) k<n))
  ≡⟨ congS (⊎.rec f e-fun) (finSplit-beta-inl k k<n (subst (k <_) (sym (+-zero n)) k<n)) ⟩
    ⊎.rec f e-fun (inl (k , k<n))
  ≡⟨ ⊎-inl-beta (Fin 0) f e-fun (k , k<n) ⟩
    f (k , k<n)
  ∎

∸-+-assoc : ∀ m n o → m ∸ n ∸ o ≡ m ∸ (n + o)
∸-+-assoc m       n       zero    = cong (m ∸_) (sym (+-zero n))
∸-+-assoc zero    zero    (suc o) = refl
∸-+-assoc zero    (suc n) (suc o) = refl
∸-+-assoc (suc m) zero    (suc o) = refl
∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc m n (suc o)

assocr-then-∸ : ∀ (k n m o : ℕ) -> k < n + (m + o) -> n + m ≤ k -> k ∸ (n + m) < o
assocr-then-∸ k n m o p q = ∸-<-lemma (n + m) o k (subst (k <_) (+-assoc n m o) p) q

finSplit-beta-assoc : ∀ {ℓ} {A : Type ℓ} {m n o : ℕ} (as : Fin m -> A) (bs : Fin n -> A) (cs : Fin o -> A)
                      -> (k : ℕ) (k<m+n : k < m + n) (k<m+n+o : k < m + (n + o))
                      -> ⊎.rec as (⊎.rec bs cs ∘ finSplit n o) (finSplit m (n + o) (k , k<m+n+o)) ≡ ⊎.rec as bs (finSplit m n (k , k<m+n))
finSplit-beta-assoc {m = m} {n = n} {o = o} as bs cs k k<m+n k<m+n+o =
  ⊎.elim (\k<m ->
            ⊎.rec as (⊎.rec bs cs ∘ finSplit n o) (finSplit m (n + o) (k , k<m+n+o))
          ≡⟨ congS (⊎.rec as (⊎.rec bs cs ∘ finSplit n o)) (finSplit-beta-inl k k<m k<m+n+o)  ⟩
            as (k , k<m)
          ≡⟨ sym (congS (⊎.rec as bs) (finSplit-beta-inl k k<m k<m+n)) ⟩
            ⊎.rec as bs (finSplit m n (k , k<m+n))
         ∎)
         (\m≤k ->
            ⊎.rec as (⊎.rec bs cs ∘ finSplit n o) (finSplit m (n + o) (k , k<m+n+o))
          ≡⟨ congS (⊎.rec as (⊎.rec bs cs ∘ finSplit n o)) (finSplit-beta-inr k k<m+n+o m≤k (∸-<-lemma m (n + o) k k<m+n+o m≤k))  ⟩
         {!   !})
  (k ≤? m)

⊕-assocr : ∀ {ℓ} {A : Type ℓ} (m n o : Array A) -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
⊕-assocr (n , as) (m , bs) (o , cs) = Array≡ (sym (+-assoc n m o)) \k k<n+m+o ->
  ⊎.elim (\k<n+m ->
            ⊎.rec (⊎.rec as bs ∘ finSplit n m) cs (finSplit (n + m) o (k , subst (k <_) (+-assoc n m o) k<n+m+o))
          ≡⟨ congS (⊎.rec (⊎.rec as bs ∘ finSplit n m) cs) (finSplit-beta-inl k k<n+m (subst (k <_) (+-assoc n m o) k<n+m+o)) ⟩
            ⊎.rec as bs (finSplit n m (k , k<n+m))
          ≡⟨ sym (finSplit-beta-assoc as bs cs k k<n+m k<n+m+o) ⟩
            ⊎.rec as (⊎.rec bs cs ∘ finSplit m o) (finSplit n (m + o) (k , k<n+m+o))
         ∎) 
         (\n+m≤k ->
            ⊎.rec (⊎.rec as bs ∘ finSplit n m) cs (finSplit (n + m) o (k , subst (k <_) (+-assoc n m o) k<n+m+o))
          ≡⟨ congS (⊎.rec (⊎.rec as bs ∘ finSplit n m) cs) (finSplit-beta-inr k (subst (k <_) (+-assoc n m o) k<n+m+o) n+m≤k (assocr-then-∸ k n m o k<n+m+o n+m≤k)) ⟩
            cs (k ∸ (n + m) , assocr-then-∸ k n m o k<n+m+o n+m≤k)
          ≡⟨ {!   !} ⟩
            ⊎.rec bs cs (finSplit m o (k , {!   !}))
          ≡⟨ {!   !} ⟩
            ⊎.rec as (⊎.rec bs cs ∘ finSplit m o) (finSplit n (m + o) (k , k<n+m+o))
         ∎)
  (k ≤? (n + m))

-- ⊕-assocr (n , as) (m , bs) (o , cs) = ΣPathP (sym (+-assoc n m o) , toPathP (funExt lemma))
--   where
--   lemma : _
--   lemma (w , p) with w ≤? (n + m)
--   lemma (w , p) | inl q with w ≤? n
--   lemma (w , p) | inl q | inl r =
--     sym (transport-filler refl (as (w , r)))
--   lemma (w , p) | inl q | inr r with (w ∸ n) ≤? m
--   lemma (w , p) | inl q | inr r | inl s =
--     _ ≡⟨ sym (transport-filler refl _) ⟩
--     bs (w ∸ n , _) ≡⟨ cong bs (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
--     bs (w ∸ n , s) ∎
--   lemma (w , p) | inl q | inr r | inr s =
--     ⊥.rec (<-asym q t)
--     where
--     t : n + m ≤ w
--     t = subst (n + m ≤_) (+-comm n (w ∸ n) ∙ ≤-∸-+-cancel r) (≤-k+ s)
--   lemma (w , p) | inr q with w ≤? n
--   lemma (w , p) | inr q | inl r =
--     ⊥.rec (¬m+n<m (≤<-trans q r))
--   lemma (w , p) | inr q | inr r with (w ∸ n) ≤? m
--   lemma (w , p) | inr q | inr r | inl s =
--     ⊥.rec (<-asym t q)
--     where
--     t : w < n + m
--     t = subst2 _<_ (≤-∸-+-cancel r) (+-comm m n) (≤-+k s)
--   lemma (w , p) | inr q | inr r | inr s =
--     _ ≡⟨ sym (transport-filler refl _) ⟩
--     cs (w ∸ (n + m) , _) ≡⟨ cong cs (Σ≡Prop (λ _ -> isProp≤) (sym (∸-+-assoc w n m))) ⟩
--     cs (w ∸ n ∸ m , _) ∎

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
  lemma (o , p) | inl q | inl r = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)
  lemma (o , p) | inl q | inr r = ⊥.rec (<-asym (pred-≤-pred q) r)
  lemma (o , p) | inr q with o ≤? n
  lemma (o , p) | inr q | inl r = ⊥.rec (¬n<m<suc-n r q)
  lemma (o , p) | inr q | inr r = cong ys (Σ≡Prop (λ _ -> isProp≤) refl)

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

    ♯-η∘ : ∀ n (xs : Fin (suc n) -> A)
      -> (η (xs fzero) ♯) 𝔜.⊕ ((n , xs ∘ fsuc) ♯)
      ≡ ((η (xs fzero) ⊕ (n , xs ∘ fsuc)) ♯)
    ♯-η∘ n xs =
      (η (xs fzero) ♯) 𝔜.⊕ ((n , xs ∘ fsuc) ♯) ≡⟨ cong (𝔜._⊕ ((n , xs ∘ fsuc) ♯)) (𝔜.unitr _) ⟩
      f (xs fzero) 𝔜.⊕ ((n , xs ∘ fsuc) ♯) ≡⟨⟩
      (suc n , xs) ♯ ≡⟨ cong (_♯) (sym (η+fsuc xs)) ⟩
      ((η (xs fzero) ⊕ (n , xs ∘ fsuc)) ♯) ∎

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
      ≡⟨ cong (𝔜._⊕ ((m , ys) ♯)) (♯-η∘ n xs) ⟩
        ((η (xs fzero) ⊕ (n , xs ∘ fsuc)) ♯) 𝔜.⊕ ((m , ys) ♯)
      ≡⟨ cong (λ z -> (z ♯) 𝔜.⊕ ((m , ys) ♯)) (η+fsuc xs) ⟩
        ((suc n , xs) ♯) 𝔜.⊕ ((m , ys) ♯) ∎

    ♯-++ : ∀ xs ys -> (xs ⊕ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
    ♯-++ (n , xs) (m , ys) = ♯-++' n xs m ys

    ♯-isMonHom : structHom 𝔄 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ ∙ sym (♯-++ (i fzero) (i fone))

  private
    arrayEquivLemma : (g : structHom 𝔄 𝔜) (n : ℕ) (xs : Fin n -> A) -> g .fst (n , xs) ≡ ((g .fst ∘ η) ♯) (n , xs)
    arrayEquivLemma (g , homMonWit) zero xs =
      g (0 , xs) ≡⟨ cong g (e-eta _ _ refl refl) ⟩
      g e ≡⟨ sym (homMonWit M.`e (lookup [])) ∙ 𝔜.e-eta ⟩
      𝔜.e ≡⟨⟩
      ((g ∘ η) ♯) (zero , xs) ∎
    arrayEquivLemma (g , homMonWit) (suc n) xs =
      g (suc n , xs) ≡⟨ cong g (sym (η+fsuc xs)) ⟩
      g (η (xs fzero) ⊕ (n , xs ∘ fsuc)) ≡⟨ sym (homMonWit M.`⊕ (lookup (η (xs fzero) ∷ₗ (n , xs ∘ fsuc) ∷ₗ []))) ⟩
      _ ≡⟨ 𝔜.⊕-eta (lookup ((η (xs fzero)) ∷ₗ (n , xs ∘ fsuc) ∷ₗ [])) g ⟩
      g (η (xs fzero)) 𝔜.⊕ g (n , xs ∘ fsuc) ≡⟨ cong (g (η (xs fzero)) 𝔜.⊕_) (arrayEquivLemma (g , homMonWit) n (xs ∘ fsuc)) ⟩
      g (η (xs fzero)) 𝔜.⊕ ((g ∘ η) ♯) (n , xs ∘ fsuc) ∎

    arrayEquivLemma-β : (g : structHom 𝔄 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ η)
    arrayEquivLemma-β g = structHom≡ 𝔄 𝔜 g (♯-isMonHom (g .fst ∘ η)) isSet𝔜 (funExt λ (n , p) -> arrayEquivLemma g n p)

  arrayEquiv : structHom 𝔄 𝔜 ≃ (A -> 𝔜 .car)
  arrayEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ η) ♯-isMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ arrayEquivLemma-β))

module ArrayDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

array-str : ∀ {n} (A : Type n) -> struct n M.MonSig
array-str A = < Array A , array-α >

array-sat : ∀ {n} {X : Type n} -> array-str X ⊨ M.MonSEq
array-sat M.`unitl ρ = ⊕-unitl (ρ fzero)
array-sat M.`unitr ρ = ⊕-unitr (ρ fzero)
array-sat M.`assocr ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)

arrayDef : ∀ {ℓ ℓ'} -> ArrayDef.Free ℓ ℓ' 2
F.Definition.Free.F arrayDef = Array
F.Definition.Free.η arrayDef = η
F.Definition.Free.α arrayDef = array-α
F.Definition.Free.sat arrayDef = array-sat
F.Definition.Free.isFree arrayDef isSet𝔜 satMon = (Free.arrayEquiv isSet𝔜 satMon) .snd

arrayIsoToList : ∀ {ℓ} {A : Type ℓ} -> Iso (Array A) (List A)
arrayIsoToList {A = A} = iso (uncurry tabulate) from tabulate-lookup from∘to
  where
  from : List A -> Array A
  from xs = length xs , lookup xs

  from∘to : ∀ xs -> from (uncurry tabulate xs) ≡ xs
  from∘to (n , xs) = ΣPathP (length-tabulate n xs , lookup-tabulate n xs)

array≡List : ∀ {ℓ} -> Array {ℓ = ℓ} ≡ List 
array≡List = funExt λ _ -> isoToPath arrayIsoToList

import Cubical.Structures.Set.Mon.List as LM

arrayDef' : ∀ {ℓ ℓ'} -> ArrayDef.Free ℓ ℓ' 2
arrayDef' {ℓ = ℓ} {ℓ' = ℓ'} = fun ArrayDef.isoAux (Array , arrayFreeAux)
  where
  listFreeAux : ArrayDef.FreeAux ℓ ℓ' 2 List
  listFreeAux = (inv ArrayDef.isoAux (LM.listDef {ℓ = ℓ} {ℓ' = ℓ'})) .snd

  arrayFreeAux : ArrayDef.FreeAux ℓ ℓ' 2 Array
  arrayFreeAux = subst (ArrayDef.FreeAux ℓ ℓ' 2) (sym array≡List) listFreeAux 