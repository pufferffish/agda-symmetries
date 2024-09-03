{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module Cubical.Structures.Set.CMon.SList.Sort.Order where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order 
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L hiding (¬_; ⊥) 

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*; [_] to [_]*; _++_ to _++*_)
import Cubical.Structures.Set.CMon.SList.Base as S
open import Cubical.Structures.Set.CMon.SList.Length as S
open import Cubical.Structures.Set.CMon.SList.Membership as S
open import Cubical.Structures.Set.CMon.SList.Sort.Base

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

module Order→Sort {A : Type ℓ} (_≤_ : A -> A -> Type ℓ) (≤-isToset : IsToset _≤_) (_≤?_ : ∀ x y -> Dec (x ≤ y)) where
  open IsToset ≤-isToset
  open Membership is-set
  open Membership* is-set

  isDiscreteA : Discrete A
  isDiscreteA x y with x ≤? y | y ≤? x
  ... | yes p | yes q = yes (is-antisym x y p q)
  ... | yes p | no ¬q = no λ r -> ¬q (subst (_≤ x) r (is-refl x))
  ... | no ¬p | yes q = no λ r -> ¬p (subst (x ≤_) r (is-refl x))
  ... | no ¬p | no ¬q = ⊥.rec $ P.rec isProp⊥ (⊎.rec ¬p ¬q) (is-strongly-connected x y)

  A-is-loset : Loset _ _
  A-is-loset = Toset→Loset (A , tosetstr _≤_ ≤-isToset) isDiscreteA

  _<_ : A -> A -> Type ℓ
  _<_ = LosetStr._<_ (A-is-loset .snd)

  <-isLoset : IsLoset _<_
  <-isLoset = LosetStr.isLoset (A-is-loset .snd)

  insert : A -> List A -> List A
  insert x [] = [ x ]
  insert x (y ∷ ys) with x ≤? y
  ... | yes p = x ∷ y ∷ ys
  ... | no ¬p = y ∷ insert x ys

  insert-β-1 : ∀ x y ys -> x ≤ y -> insert x (y ∷ ys) ≡ x ∷ y ∷ ys
  insert-β-1 x y ys p with x ≤? y
  ... | yes _ = refl
  ... | no ¬p = ⊥.rec (¬p p)

  insert-β-2 : ∀ x y ys -> ¬ (x ≤ y) -> insert x (y ∷ ys) ≡ y ∷ insert x ys
  insert-β-2 x y ys ¬p with x ≤? y
  ... | yes p = ⊥.rec (¬p p)
  ... | no ¬_ = refl

  insert-≤ : ∀ x y xs ys -> insert x (insert y xs) ≡ x ∷ y ∷ ys -> x ≤ y
  insert-≤ x y [] ys p with x ≤? y
  ... | yes x≤y = x≤y
  ... | no ¬x≤y = subst (_≤ y) (cons-inj₁ p) (is-refl y)
  insert-≤ x y (z ∷ zs) ys p with y ≤? z
  ... | yes y≤z = lemma
    where
    lemma : x ≤ y
    lemma with x ≤? y
    ... | yes x≤y = x≤y
    ... | no ¬x≤y = subst (_≤ y) (cons-inj₁ p) (is-refl y)
  ... | no ¬y≤z = lemma
    where
    lemma : x ≤ y
    lemma with x ≤? z
    ... | yes x≤z = subst (x ≤_) (cons-inj₁ (cons-inj₂ p)) x≤z
    ... | no ¬x≤z = ⊥.rec (¬x≤z (subst (_≤ z) (cons-inj₁ p) (is-refl z)))

  insert-cons : ∀ x xs ys -> x ∷ xs ≡ insert x ys -> xs ≡ ys
  insert-cons x xs [] p = cons-inj₂ p
  insert-cons x xs (y ∷ ys) p with x ≤? y
  ... | yes x≤y = cons-inj₂ p
  ... | no ¬x≤y = ⊥.rec (¬x≤y (subst (x ≤_) (cons-inj₁ p) (is-refl x)))

  private
    not-total-impossible : ∀ {x y} -> ¬(x ≤ y) -> ¬(y ≤ x) -> ⊥
    not-total-impossible {x} {y} p q =
      P.rec isProp⊥ (⊎.rec p q) (is-strongly-connected x y)

  insert-insert : ∀ x y xs -> insert x (insert y xs) ≡ insert y (insert x xs)
  insert-insert x y [] with x ≤? y | y ≤? x
  ... | yes x≤y | no ¬y≤x = refl
  ... | no ¬x≤y | yes y≤x = refl
  ... | no ¬x≤y | no ¬y≤x = ⊥.rec (not-total-impossible ¬x≤y ¬y≤x)
  ... | yes x≤y | yes y≤x = let x≡y = is-antisym x y x≤y y≤x in cong₂ (λ u v -> u ∷ v ∷ []) x≡y (sym x≡y)
  insert-insert x y (z ∷ zs) with y ≤? z | x ≤? z
  ... | yes y≤z | yes x≤z = case1 y≤z x≤z
    where
    case1 : y ≤ z -> x ≤ z -> insert x (y ∷ z ∷ zs) ≡ insert y (x ∷ z ∷ zs)
    case1 y≤z x≤z with x ≤? y | y ≤? x
    ... | yes x≤y | yes y≤x = let x≡y = is-antisym x y x≤y y≤x in cong₂ (λ u v -> (u ∷ v ∷ z ∷ zs)) x≡y (sym x≡y)
    ... | yes x≤y | no ¬y≤x = sym (congS (x ∷_) (insert-β-1 y z zs y≤z))
    ... | no ¬x≤y | yes y≤x = congS (y ∷_) (insert-β-1 x z zs x≤z)
    ... | no ¬x≤y | no ¬y≤x = ⊥.rec (not-total-impossible ¬x≤y ¬y≤x)
  ... | yes y≤z | no ¬x≤z = case2 y≤z ¬x≤z
    where
    case2 : y ≤ z -> ¬(x ≤ z) -> insert x (y ∷ z ∷ zs) ≡ insert y (z ∷ insert x zs)
    case2 y≤z ¬x≤z with x ≤? y
    ... | yes x≤y = ⊥.rec (¬x≤z (is-trans x y z x≤y y≤z))
    ... | no ¬x≤y = congS (y ∷_) (insert-β-2 x z zs ¬x≤z) ∙ sym (insert-β-1 y z _ y≤z)
  ... | no ¬y≤z | yes x≤z = case3 ¬y≤z x≤z
    where
    case3 : ¬(y ≤ z) -> x ≤ z -> insert x (z ∷ insert y zs) ≡ insert y (x ∷ z ∷ zs)
    case3 ¬y≤z x≤z with y ≤? x
    ... | yes y≤x = ⊥.rec (¬y≤z (is-trans y x z y≤x x≤z))
    ... | no ¬y≤x = insert-β-1 x z _ x≤z ∙ congS (x ∷_) (sym (insert-β-2 y z zs ¬y≤z))
  ... | no ¬y≤z | no ¬x≤z =
    insert x (z ∷ insert y zs) ≡⟨ insert-β-2 x z _ ¬x≤z ⟩
    z ∷ insert x (insert y zs) ≡⟨ congS (z ∷_) (insert-insert x y zs) ⟩
    z ∷ insert y (insert x zs) ≡⟨ sym (insert-β-2 y z _ ¬y≤z) ⟩
    insert y (z ∷ insert x zs) ∎

  sort : SList A -> List A
  sort = Elim.f []
    (λ x xs -> insert x xs)
    (λ x y xs -> insert-insert x y xs)
    (λ _ -> isOfHLevelList 0 is-set)

  insert-is-permute : ∀ x xs -> list→slist (x ∷ xs) ≡ list→slist (insert x xs)
  insert-is-permute x [] = refl
  insert-is-permute x (y ∷ ys) with x ≤? y
  ... | yes p = refl
  ... | no ¬p =
    x ∷* y ∷* list→slist ys ≡⟨ swap x y _ ⟩
    y ∷* x ∷* list→slist ys ≡⟨ congS (y ∷*_) (insert-is-permute x ys) ⟩
    y ∷* list→slist (insert x ys) ∎

  open Sort is-set

  sort-is-permute : is-section sort
  sort-is-permute = ElimProp.f (trunc _ _) refl lemma
    where
    lemma : ∀ x {xs} p -> list→slist (sort (x ∷* xs)) ≡ x ∷* xs
    lemma x {xs} p = sym $
      x ∷* xs ≡⟨ congS (x ∷*_) (sym p) ⟩
      list→slist (x ∷ sort xs) ≡⟨ insert-is-permute x (sort xs) ⟩
      list→slist (insert x (sort xs)) ≡⟨⟩
      list→slist (sort (x ∷* xs)) ∎

  tail-is-sorted : ∀ x xs -> is-sorted sort (x ∷ xs) -> is-sorted sort xs
  tail-is-sorted x xs = P.rec squash₁ (uncurry lemma)
    where
    lemma : ∀ ys p -> is-sorted sort xs
    lemma ys p = ∣ (list→slist xs) , sym (insert-cons x _ _ sort-proof) ∣₁
      where
      ys-proof : ys ≡ x ∷* list→slist xs
      ys-proof = sym (sort-is-permute ys) ∙ (congS list→slist p)
      sort-proof : x ∷ xs ≡ insert x (sort (list→slist xs))
      sort-proof = sym p ∙ congS sort ys-proof

  -- Inductive definition of Sorted
  data Sorted : List A -> Type ℓ where
    sorted-nil : Sorted []
    sorted-one : ∀ x -> Sorted [ x ]
    sorted-cons : ∀ x y zs -> x ≤ y -> Sorted (y ∷ zs) -> Sorted (x ∷ y ∷ zs)

  open Sort.Section is-set

  is-sort' : (SList A -> List A) -> Type _
  is-sort' f = (∀ xs -> list→slist (f xs) ≡ xs) × (∀ xs -> ∥ Sorted (f xs) ∥₁)

  tail-sorted' : ∀ {x xs} -> Sorted (x ∷ xs) -> Sorted xs 
  tail-sorted' (sorted-one ._) = sorted-nil
  tail-sorted' (sorted-cons ._ _ _ _ p) = p

  ≤-tail : ∀ {x y ys} -> y ∈ (x ∷ ys) -> Sorted (x ∷ ys) -> x ≤ y
  ≤-tail {y = y} p (sorted-one x) = subst (_≤ y) (x∈[y]→x≡y y x p) (is-refl y)
  ≤-tail {x} {y = z} p (sorted-cons x y zs q r) =
    P.rec (is-prop-valued x z)
      (⊎.rec
        (λ z≡x -> subst (x ≤_) (sym z≡x) (is-refl x))
        (λ z∈ys -> is-trans x y z q (≤-tail z∈ys r))
      ) p
  
  smallest-sorted : ∀ x xs -> (∀ y -> y ∈ xs -> x ≤ y) -> Sorted xs -> Sorted (x ∷ xs)
  smallest-sorted x .[] p sorted-nil =
    sorted-one x
  smallest-sorted x .([ y ]) p (sorted-one y) =
    sorted-cons x y [] (p y (x∈[x] y)) (sorted-one y)
  smallest-sorted x .(_ ∷ _ ∷ _) p (sorted-cons y z zs y≤z r) =
    sorted-cons x y (z ∷ zs) (p y (x∈xs y (z ∷ zs))) (smallest-sorted y (z ∷ zs) lemma r)
    where
    lemma : ∀ a -> a ∈ (z ∷ zs) -> y ≤ a
    lemma a = P.rec (is-prop-valued y a) $ ⊎.rec
      (λ a≡z -> subst (y ≤_) (sym a≡z) y≤z)
      (λ a∈zs -> is-trans y z a y≤z (≤-tail (L.inr a∈zs) r))

  insert-∈ : ∀ {x} {y} ys -> x ∈ insert y ys -> x ∈ (y ∷ ys)
  insert-∈ {x} {y} ys p = ∈*→∈ x (y ∷ ys)
    (subst (x ∈*_) (sym (insert-is-permute y ys)) (∈→∈* x (insert y ys) p))

  insert-is-sorted : ∀ x xs -> Sorted xs -> Sorted (insert x xs)
  insert-is-sorted x [] p = sorted-one x
  insert-is-sorted x (y ∷ ys) p with x ≤? y
  ... | yes q = sorted-cons x y ys q p
  ... | no ¬q = smallest-sorted y (insert x ys) (lemma ys p) IH
    where
    IH : Sorted (insert x ys)
    IH = insert-is-sorted x ys (tail-sorted' p)
    y≤x : y ≤ x
    y≤x = P.rec (is-prop-valued y x) (⊎.rec (idfun _) (⊥.rec ∘ ¬q)) (is-strongly-connected y x)
    lemma : ∀ zs -> Sorted (y ∷ zs) -> ∀ z -> z ∈ insert x zs → y ≤ z
    lemma zs p z r = P.rec (is-prop-valued y z)
      (⊎.rec (λ z≡x -> subst (y ≤_) (sym z≡x) y≤x) (λ z∈zs -> ≤-tail (L.inr z∈zs) p)) (insert-∈ zs r)

  sort-is-sorted' : ∀ xs -> ∥ Sorted (sort xs) ∥₁
  sort-is-sorted' = ElimProp.f squash₁ ∣ sorted-nil ∣₁
    λ x -> P.rec squash₁ λ p -> ∣ (insert-is-sorted x _ p) ∣₁

  sort-is-sorted'' : ∀ xs -> is-sorted sort xs -> ∥ Sorted xs ∥₁
  sort-is-sorted'' xs = P.rec squash₁ λ (ys , p) ->
    P.map (subst Sorted p) (sort-is-sorted' ys)

  -- Step 1. show both sort xs and sort->order->sort xs give sorted list
  -- Step 2. apply this lemma
  -- Step 3. get sort->order->sort = sort
  unique-sorted-xs : ∀ xs ys -> list→slist xs ≡ list→slist ys -> Sorted xs -> Sorted ys -> xs ≡ ys
  unique-sorted-xs [] [] p xs-sorted ys-sorted = refl
  unique-sorted-xs [] (y ∷ ys) p xs-sorted ys-sorted = ⊥.rec (znots (congS S.length p))
  unique-sorted-xs (x ∷ xs) [] p xs-sorted ys-sorted = ⊥.rec (snotz (congS S.length p))
  unique-sorted-xs (x ∷ xs) (y ∷ ys) p xs-sorted ys-sorted =
    cong₂ _∷_ x≡y (unique-sorted-xs xs ys xs≡ys (tail-sorted' xs-sorted) (tail-sorted' ys-sorted))
    where
    x≤y : x ≤ y
    x≤y = ≤-tail (∈*→∈ y (x ∷ xs) (subst (y ∈*_) (sym p) (L.inl refl))) xs-sorted
    y≤x : y ≤ x
    y≤x = ≤-tail (∈*→∈ x (y ∷ ys) (subst (x ∈*_) p (L.inl refl))) ys-sorted
    x≡y : x ≡ y
    x≡y = is-antisym x y x≤y y≤x
    xs≡ys : list→slist xs ≡ list→slist ys
    xs≡ys =
      list→slist xs ≡⟨ remove1-≡-lemma isDiscreteA (list→slist xs) refl ⟩
      remove1 isDiscreteA x (list→slist (x ∷ xs)) ≡⟨ congS (remove1 isDiscreteA x) p ⟩
      remove1 isDiscreteA x (list→slist (y ∷ ys)) ≡⟨ sym (remove1-≡-lemma isDiscreteA (list→slist ys) x≡y) ⟩
      list→slist ys ∎
  
  unique-sort : ∀ f -> is-sort' f -> f ≡ sort
  unique-sort f (f-is-permute , f-is-sorted) = funExt λ xs ->
    P.rec2 (isOfHLevelList 0 is-set _ _)
      (unique-sorted-xs (f xs) (sort xs) (f-is-permute xs ∙ sym (sort-is-permute xs)))
      (f-is-sorted xs)
      (sort-is-sorted' xs)

  unique-sort' : ∀ f xs -> is-sort' f -> f xs ≡ sort xs
  unique-sort' f xs p = congS (λ g -> g xs) (unique-sort f p)

  private
    sort→order-lemma : ∀ x y xs -> is-sorted sort (x ∷ y ∷ xs) -> x ≤ y
    sort→order-lemma x y xs = P.rec (is-prop-valued x y) (uncurry lemma)
      where
      lemma : ∀ ys p -> x ≤ y
      lemma ys p = insert-≤ x y (sort tail) xs (congS sort tail-proof ∙ p)
        where
        tail : SList A
        tail = list→slist xs
        tail-proof : x ∷* y ∷* tail ≡ ys
        tail-proof = sym (congS list→slist p) ∙ sort-is-permute ys

    sort→order : ∀ x y xs -> is-sorted sort (x ∷ xs) -> y ∈ (x ∷ xs) -> x ≤ y
    sort→order x y [] p y∈xs = subst (_≤ y) (x∈[y]→x≡y y x y∈xs) (is-refl y)
    sort→order x y (z ∷ zs) p y∈x∷z∷zs with isDiscreteA x y
    ... | yes x≡y = subst (x ≤_) x≡y (is-refl x)
    ... | no ¬x≡y =
      P.rec (is-prop-valued x y) (⊎.rec (⊥.rec ∘ ¬x≡y ∘ sym) lemma) y∈x∷z∷zs
      where
      lemma : y ∈ (z ∷ zs) -> x ≤ y
      lemma y∈z∷zs = is-trans x z y
        (sort→order-lemma x z zs p)
        (sort→order z y zs (tail-is-sorted x (z ∷ zs) p) y∈z∷zs)

  sort-is-head-least : is-head-least sort
  sort-is-head-least x y xs p y∈xs = ∣ (x ∷* y ∷* []* , insert-β-1 x y [] (sort→order x y xs p y∈xs)) ∣₁

  sort-is-sort-section : is-sort-section sort
  sort-is-sort-section = sort-is-permute , sort-is-head-least , tail-is-sorted

  -- counter example that obeys is-head-least and not tail-sort

  swap1-2 : List A -> List A
  swap1-2 [] = []
  swap1-2 (x ∷ []) = x ∷ []
  swap1-2 (x ∷ y ∷ xs) = y ∷ x ∷ xs

  swap1-2-id : ∀ xs -> swap1-2 (swap1-2 xs) ≡ xs
  swap1-2-id [] = refl
  swap1-2-id (x ∷ []) = refl
  swap1-2-id (x ∷ y ∷ xs) = refl

  swap2-3 : List A -> List A
  swap2-3 [] = []
  swap2-3 (x ∷ xs) = x ∷ swap1-2 xs

  swap2-3-id : ∀ xs -> swap2-3 (swap2-3 xs) ≡ xs
  swap2-3-id [] = refl
  swap2-3-id (x ∷ xs) = congS (x ∷_) (swap1-2-id xs)

  swap2-3-is-permute : ∀ f -> is-section f -> is-section (swap2-3 ∘ f)
  swap2-3-is-permute f f-is-permute xs with f xs | inspect f xs
  ... | [] | [ p ]ᵢ = sym (congS list→slist p) ∙ f-is-permute xs
  ... | x ∷ [] | [ p ]ᵢ = sym (congS list→slist p) ∙ f-is-permute xs
  ... | x ∷ y ∷ [] | [ p ]ᵢ = sym (congS list→slist p) ∙ f-is-permute xs
  ... | x ∷ y ∷ z ∷ ys | [ p ]ᵢ =
    x ∷* z ∷* y ∷* list→slist ys ≡⟨ congS (x ∷*_) (swap z y (list→slist ys)) ⟩
    x ∷* y ∷* z ∷* list→slist ys ≡⟨ sym (congS list→slist p) ⟩
    list→slist (f xs) ≡⟨ f-is-permute xs ⟩
    xs ∎

  head-least-only : SList A -> List A
  head-least-only = swap2-3 ∘ sort

  head-least-only-is-permute : is-section head-least-only
  head-least-only-is-permute = swap2-3-is-permute sort sort-is-permute

  private
    head-least-is-same-for-2 : ∀ u v -> is-sorted sort (u ∷ v ∷ []) -> is-sorted head-least-only (u ∷ v ∷ [])
    head-least-is-same-for-2 u v = P.map λ (ys , q) -> ys , congS swap2-3 q

    head-least→sorted : ∀ x xs -> is-sorted head-least-only (x ∷ xs) -> is-sorted sort (x ∷ swap1-2 xs)
    head-least→sorted x [] =
      P.map λ (ys , q) -> ys , sym (swap2-3-id (sort ys)) ∙ congS swap2-3 q
    head-least→sorted x (y ∷ []) =
      P.map λ (ys , q) -> ys , sym (swap2-3-id (sort ys)) ∙ congS swap2-3 q
    head-least→sorted x (y ∷ z ∷ xs) =
      P.map λ (ys , q) -> ys , sym (swap2-3-id (sort ys)) ∙ congS swap2-3 q

    swap1-2-∈ : ∀ x xs -> x ∈ xs -> x ∈ swap1-2 xs
    swap1-2-∈ x [] x∈ = x∈
    swap1-2-∈ x (y ∷ []) x∈ = x∈
    swap1-2-∈ x (y ∷ z ∷ xs) = P.rec squash₁
      (⊎.rec (L.inr ∘ L.inl) (P.rec squash₁ (⊎.rec L.inl (L.inr ∘ L.inr))))

    swap2-3-∈ : ∀ x xs -> x ∈ xs -> x ∈ swap2-3 xs
    swap2-3-∈ x (y ∷ xs) = P.rec squash₁ (⊎.rec L.inl (L.inr ∘ swap1-2-∈ x xs))

    is-sorted→≤ : ∀ {x y} -> is-sorted sort (x ∷ y ∷ []) -> x ≤ y
    is-sorted→≤ {x} {y} p = P.rec (is-prop-valued x y)
      (≤-tail {ys = y ∷ []} (L.inr (L.inl refl)))
      (sort-is-sorted'' (x ∷ y ∷ []) p)

    head-least-tail-sort→x≡y : ∀ x y -> is-tail-sort head-least-only -> x ≤ y -> x ≡ y
    head-least-tail-sort→x≡y x y h-tail-sort x≤y =
      is-antisym x y x≤y (is-sorted→≤ (lemma1 ∣ x ∷* x ∷* y ∷* []* , lemma2 ∣₁))
      where
      -- [1, 2, 3] sorted by sort -> [1, 3, 2] sorted by head-least -> [3, 2] sorted by head-least -> [3, 2] sorted by sort
      lemma1 : is-sorted sort (x ∷ x ∷ y ∷ []) -> is-sorted sort (y ∷ x ∷ [])
      lemma1 = P.rec squash₁ λ (ys , q) -> head-least→sorted y [ x ] (h-tail-sort x _ ∣ ys , congS swap2-3 q ∣₁) 
      lemma2 : sort (x ∷* x ∷* [ y ]*) ≡ x ∷ x ∷ y ∷ []
      lemma2 =
        insert x (insert x [ y ]) ≡⟨ congS (insert x) (insert-β-1 x y [] x≤y) ⟩
        insert x (x ∷ y ∷ []) ≡⟨ insert-β-1 x x [ y ] (is-refl x) ⟩
        x ∷ x ∷ [ y ] ∎

  head-least-only-is-head-least : is-head-least head-least-only
  head-least-only-is-head-least x y xs p y∈xs = head-least-is-same-for-2 x y
    (sort-is-head-least x y (swap1-2 xs) (head-least→sorted x xs p) (swap2-3-∈ y (x ∷ xs) y∈xs))

  head-least-tail-sort→isProp-A : is-tail-sort head-least-only -> isProp A
  head-least-tail-sort→isProp-A h-tail-sort x y = P.rec (is-set _ _)
    (⊎.rec (head-least-tail-sort→x≡y x y h-tail-sort) (sym ∘ (head-least-tail-sort→x≡y y x h-tail-sort)))
    (is-strongly-connected x y)

module Order→Sort-Example where

  ≤ℕ-isToset : IsToset _≤ℕ_
  ≤ℕ-isToset = istoset isSetℕ
    (λ _ _ -> isProp≤)
    (λ _ -> ≤-refl)
    (λ _ _ _ -> ≤-trans)
    (λ _ _ -> ≤-antisym)
    lemma
    where
    <→≤ : ∀ {n m} -> n <ℕ m -> n ≤ℕ m
    <→≤ (k , p) = suc k , sym (+-suc k _) ∙ p
    lemma : BinaryRelation.isStronglyConnected _≤ℕ_
    lemma x y = ∣ ⊎.rec ⊎.inl (_⊎_.inr ∘ <→≤) (splitℕ-≤ x y) ∣₁

  open Order→Sort _≤ℕ_ ≤ℕ-isToset ≤Dec
 
  _ : sort (4 ∷* 6 ∷* 1 ∷* 2 ∷* []*) ≡ (1 ∷ 2 ∷ 4 ∷ 6 ∷ [])
  _ = refl
