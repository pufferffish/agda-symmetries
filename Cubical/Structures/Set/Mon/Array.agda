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

finCombine : ∀ m n -> Fin m ⊎ Fin n -> Fin (m + n)
finCombine m n (inl (k , p)) = k , o<m→o<m+n m n k p
finCombine m n (inr (k , p)) = m + k , <-k+ p

finSplit∘finCombine : ∀ m n x -> (finSplit m n ∘ finCombine m n) x ≡ x
finSplit∘finCombine m n (inl (k , p)) with k ≤? m
... | inl q = cong inl (Σ≡Prop (λ _ → isProp≤) refl)
... | inr q = ⊥.rec (¬-<-and-≥ p q)
finSplit∘finCombine m n (inr (k , p)) with (m + k) ≤? m
... | inl q = ⊥.rec (¬m+n<m q)
... | inr q = cong inr (Σ≡Prop (λ _ → isProp≤) lemma)
  where
  lemma : m + k ∸ m ≡ k
  lemma = subst (λ - -> - ∸ m ≡ k) (+-comm k m) (m+n∸n=m m k)

finCombine∘finSplit : ∀ m n x -> (finCombine m n ∘ finSplit m n) x ≡ x
finCombine∘finSplit m n (o , p) with o ≤? m
... | inl q = Σ≡Prop (λ _ → isProp≤) refl
... | inr q = Σ≡Prop (λ _ → isProp≤) (∸-lemma q)

Fin≅Fin+Fin : ∀ m n -> Fin (m + n) ≃ (Fin m ⊎ Fin n)
Fin≅Fin+Fin m n = isoToEquiv (iso (finSplit m n) (finCombine m n) (finSplit∘finCombine m n) (finCombine∘finSplit m n))

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

array-sat : ∀ {n} {X : Type n} -> < Array X , array-α > ⊨ M.MonSEq
array-sat M.`unitl ρ = ⊕-unitl (ρ fzero)
array-sat M.`unitr ρ = ⊕-unitr (ρ fzero)
array-sat M.`assocr ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)

arrayDef : ArrayDef.Free 2
F.Definition.Free.F arrayDef = Array
F.Definition.Free.η arrayDef = η
F.Definition.Free.α arrayDef = array-α
F.Definition.Free.sat arrayDef = array-sat
F.Definition.Free.isFree arrayDef isSet𝔜 satMon = (Free.arrayEquiv isSet𝔜 satMon) .snd
