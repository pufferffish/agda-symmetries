{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module Cubical.Structures.Set.CMon.SList.Sort where

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
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L

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

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

head-maybe : List A -> Maybe A
head-maybe [] = nothing
head-maybe (x ∷ xs) = just x

Permutation : List A -> List A -> Type _
Permutation xs ys = list→slist xs ≡ list→slist ys

module Sort {A : Type ℓ} (_≤_ : A -> A -> Type ℓ) (≤-isToset : IsToset _≤_) where

  open IsToset ≤-isToset
  open Membership is-set

  data Sorted : List A -> Type ℓ where
    sorted-nil : Sorted []
    sorted-one : ∀ x -> Sorted [ x ]
    sorted-cons : ∀ x y zs -> x ≤ y -> Sorted (y ∷ zs) -> Sorted (x ∷ y ∷ zs)

  is-sort : (List A -> List A) -> Type _
  is-sort f = ∀ xs -> Permutation xs (f xs) × Sorted (f xs)

  tail-sorted : ∀ {x xs} -> Sorted (x ∷ xs) -> Sorted xs 
  tail-sorted (sorted-one ._) = sorted-nil
  tail-sorted (sorted-cons ._ _ _ _ p) = p

  ≤-tail : ∀ {x y ys} -> y ∈ ys -> Sorted (x ∷ ys) -> x ≤ y
  ≤-tail {x} {y = z} p (sorted-cons x y zs q r) =
    P.rec (is-prop-valued x z)
      (⊎.rec (λ z≡y -> subst (x ≤_) (sym z≡y) q) (λ z∈zs -> is-trans x y z q (≤-tail z∈zs r))) p

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
      (λ a∈zs -> is-trans y z a y≤z (≤-tail a∈zs r))

module Order→Sort {A : Type ℓ} (_≤_ : A -> A -> Type ℓ) (≤-isToset : IsToset _≤_) (_≤?_ : ∀ x y -> Dec (x ≤ y)) where

  open IsToset ≤-isToset
  open Sort _≤_ ≤-isToset
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

  sort : List A -> List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

  insert-is-perm : ∀ x xs -> Permutation (x ∷ xs) (insert x xs)
  insert-is-perm x [] = refl
  insert-is-perm x (y ∷ ys) with x ≤? y
  ... | yes p = refl
  ... | no ¬p =
    x ∷* y ∷* list→slist ys ≡⟨ swap x y _ ⟩
    y ∷* x ∷* list→slist ys ≡⟨ congS (y ∷*_) (insert-is-perm x ys) ⟩
    y ∷* list→slist (insert x ys) ∎

  sort-is-perm : ∀ xs -> Permutation xs (sort xs)
  sort-is-perm [] = refl
  sort-is-perm (x ∷ xs) =
    x ∷* list→slist xs ≡⟨ congS (x ∷*_) (sort-is-perm xs) ⟩
    list→slist (x ∷ sort xs) ≡⟨ insert-is-perm x (sort xs) ⟩
    list→slist (insert x (sort xs)) ∎

  insert-∈ : ∀ {x} {y} ys -> x ∈ insert y ys -> x ∈ (y ∷ ys)
  insert-∈ {x} {y} ys p = ∈*→∈ x (y ∷ ys)
    (subst (x ∈*_) (sym (insert-is-perm y ys)) (∈→∈* x (insert y ys) p))

  insert-is-sorted : ∀ x xs -> Sorted xs -> Sorted (insert x xs)
  insert-is-sorted x [] p = sorted-one x
  insert-is-sorted x (y ∷ ys) p with x ≤? y
  ... | yes q = sorted-cons x y ys q p
  ... | no ¬q = smallest-sorted y (insert x ys) (lemma ys p) IH
    where
    IH : Sorted (insert x ys)
    IH = insert-is-sorted x ys (tail-sorted p)
    y≤x : y ≤ x
    y≤x = P.rec (is-prop-valued y x) (⊎.rec (idfun _) (⊥.rec ∘ ¬q)) (is-strongly-connected y x)
    lemma : ∀ zs -> Sorted (y ∷ zs) -> ∀ z -> z ∈ insert x zs → y ≤ z
    lemma zs p z r = P.rec (is-prop-valued y z)
      (⊎.rec (λ z≡x -> subst (y ≤_) (sym z≡x) y≤x) (λ z∈zs -> ≤-tail z∈zs p)) (insert-∈ zs r)

  sort-xs-is-sorted : ∀ xs -> Sorted (sort xs)
  sort-xs-is-sorted [] = sorted-nil
  sort-xs-is-sorted (x ∷ xs) = insert-is-sorted x (sort xs) (sort-xs-is-sorted xs)

  sort-is-sort : is-sort sort
  sort-is-sort xs = sort-is-perm xs , sort-xs-is-sorted xs

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

  _ : sort (4 ∷ 6 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 4 ∷ 6 ∷ [])
  _ = refl

-- module Sort→Order (isSetA : isSet A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where
-- 
--   isSetMaybeA : isSet (Maybe A)
--   isSetMaybeA = isOfHLevelMaybe 0 isSetA
-- 
--   private
--     module 𝔖 = M.CMonSEq < SList A , slist-α > slist-sat
--   
--   open Membership isSetA
--   open Membership* isSetA
-- 
--   private
--     list→slist-η : ∀ xs -> (x : A) -> list→slist xs ≡ [ x ]* -> xs ≡ [ x ]
--     list→slist-η [] x p = ⊥.rec (znots (congS S.length p))
--     list→slist-η (x ∷ []) y p = congS [_] ([-]-inj {ϕ = isSetA} p)
--     list→slist-η (x ∷ y ∷ xs) z p = ⊥.rec (snotz (injSuc (congS S.length p)))
-- 
--     sort-length≡-α : ∀ (xs : List A) -> L.length xs ≡ S.length (list→slist xs)
--     sort-length≡-α [] = refl
--     sort-length≡-α (x ∷ xs) = congS suc (sort-length≡-α xs)
-- 
--     sort-length≡ : ∀ xs -> L.length (sort xs) ≡ S.length xs
--     sort-length≡ xs = sort-length≡-α (sort xs) ∙ congS S.length (sort≡ xs)
-- 
--     length-0 : ∀ (xs : List A) -> L.length xs ≡ 0 -> xs ≡ []
--     length-0 [] p = refl
--     length-0 (x ∷ xs) p = ⊥.rec (snotz p)
-- 
--     sort-[] : ∀ xs -> sort xs ≡ [] -> xs ≡ []*
--     sort-[] xs p = sym (sort≡ xs) ∙ congS list→slist p
-- 
--     sort-[]' : sort []* ≡ []
--     sort-[]' = length-0 (sort []*) (sort-length≡ []*)
-- 
--     sort-[-] : ∀ x -> sort [ x ]* ≡ [ x ]
--     sort-[-] x = list→slist-η (sort [ x ]*) x (sort≡ [ x ]*)
-- 
--     list→slist-[] : (xs : List A) -> list→slist xs ≡ []* -> xs ≡ []
--     list→slist-[] [] p = refl
--     list→slist-[] (x ∷ xs) p = ⊥.rec (snotz (congS S.length p))
-- 
--     Prec : {X P : Type ℓ} -> isProp P -> ∥ X ∥₁ -> (X -> P) -> P
--     Prec x y z = P.rec x z y
-- 
--     A≡ : A -> A -> hProp _
--     A≡ x y = (x ≡ y) , isSetA x y
-- 
--     just≡ : A -> A -> hProp _
--     just≡ x y = (just x ≡ just y) , isSetMaybeA _ _
-- 
--     maybe≡ : Maybe A -> Maybe A -> hProp _
--     maybe≡ x y = (x ≡ y) , isSetMaybeA _ _
-- 
--   sort-∈ : ∀ x xs -> x ∈* xs -> x ∈ sort xs
--   sort-∈ x xs p = ∈*→∈ x (sort xs) (subst (x ∈*_) (sym (sort≡ xs)) p)
-- 
--   sort-∈* : ∀ x xs -> x ∈ sort xs -> x ∈* xs
--   sort-∈* x xs p = subst (x ∈*_) (sort≡ xs) (∈→∈* x (sort xs) p)
-- 
--   least : SList A -> Maybe A
--   least xs = head-maybe (sort xs)
-- 
--   least-nothing : ∀ xs -> least xs ≡ nothing -> xs ≡ []*
--   least-nothing xs p with sort xs | inspect sort xs
--   ... | []     | [ q ]ᵢ = sort-[] xs q
--   ... | y ∷ ys | [ q ]ᵢ = ⊥.rec (¬just≡nothing p)
-- 
--   least-Σ : ∀ x xs -> least xs ≡ just x -> Σ[ ys ∈ List A ] (sort xs ≡ x ∷ ys)
--   least-Σ x xs p with sort xs
--   ... | []     = ⊥.rec (¬nothing≡just p)
--   ... | y ∷ ys = ys , congS (_∷ ys) (just-inj y x p)
-- 
--   least-in : ∀ x xs -> least xs ≡ just x -> x ∈* xs
--   least-in x xs p =
--     let (ys , q) = least-Σ x xs p
--         x∷ys≡xs = congS list→slist (sym q) ∙ sort≡ xs
--     in subst (x ∈*_) x∷ys≡xs (x∈*xs x (list→slist ys))
-- 
--   least-choice-prop : ∀ x y -> hProp _
--   least-choice-prop x y =
--     (maybe≡ (least (x ∷* [ y ]*)) (just x))
--     ⊔ (maybe≡ (least (x ∷* [ y ]*)) (just y))
-- 
--   least-choice : ∀ x y -> ⟨ least-choice-prop x y ⟩
--   least-choice x y with least (x ∷* [ y ]*) | inspect least (x ∷* [ y ]*)
--   ... | nothing | [ p ]ᵢ =
--     ⊥.rec (snotz (congS S.length (least-nothing (x ∷* [ y ]*) p)))
--   ... | just z  | [ p ]ᵢ =
--     ⊔-elim (A≡ z x) ((A≡ z y) ⊔ (⊥* , isProp⊥*)) (λ _ -> (just≡ z x) ⊔ (just≡ z y))
--       (λ q -> L.inl (congS just q))
--       (L.inr ∘ ⊔-elim (A≡ z y) (⊥* , isProp⊥*) (λ _ -> (just≡ z y)) (congS just) ⊥.rec*)
--       (least-in z (x ∷* [ y ]*) p)
-- 
--   _≤_ : A -> A -> Type _
--   x ≤ y = least (x ∷* y ∷* []*) ≡ just x
-- 
--   isProp-≤ : ∀ {a} {b} -> isProp (a ≤ b)
--   isProp-≤  = isSetMaybeA _ _
-- 
--   ≤-Prop : ∀ x y -> hProp _
--   ≤-Prop x y = (x ≤ y) , isProp-≤
-- 
--   refl-≤ : ∀ x -> x ≤ x
--   refl-≤ x = Prec isProp-≤ (least-choice x x) (⊎.rec (idfun _) (idfun _))
-- 
--   antisym-≤ : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y
--   antisym-≤ x y p q = Prec (isSetA x y) (least-choice x y) $
--     ⊎.rec
--       (λ xy -> just-inj x y $
--         just x ≡⟨ sym xy ⟩
--         least (x ∷* y ∷* []*) ≡⟨ congS least (swap x y []*) ⟩
--         least (y ∷* x ∷* []*) ≡⟨ q ⟩
--         just y
--       ∎)
--       (λ yx -> just-inj x y $
--         just x ≡⟨ sym p ⟩
--         least (x ∷* [ y ]*) ≡⟨ yx ⟩
--         just y
--       ∎)
-- 
--   total-≤ : ∀ x y -> (x ≤ y) ⊔′ (y ≤ x)
--   total-≤ x y = Prec squash₁ (least-choice x y) $ ⊎.rec
--     L.inl
--     (λ p -> L.inr $
--       least (y ∷* [ x ]*) ≡⟨ congS least (swap y x []*) ⟩
--       least (x ∷* [ y ]*) ≡⟨ p ⟩
--       just y
--     ∎)
-- 
--   x≤y→sort : ∀ x y -> x ≤ y -> sort (x ∷* y ∷* []*) ≡ x ∷ y ∷ []
--   x≤y→sort x y x≤y with sort (x ∷* [ y ]*) | inspect sort (x ∷* [ y ]*)
--   ... | []             | [ p ]ᵢ = {!   !}
--   ... | a ∷ []         | [ p ]ᵢ = {!   !}
--   ... | a ∷ b ∷ c ∷ as | [ p ]ᵢ = {!   !}
--   ... | a ∷ b ∷ []     | [ p ]ᵢ =
--     cong₂ (λ u v → u ∷ [ v ]) (just-inj _ _ x≤y) $ ⊔-elim (A≡ y a) (∈Prop y [ b ]) (λ _ -> A≡ b y)
--       (λ y≡a ->
--         {!   !}
--       )
--       (λ y∈[b] ->
--         sym (x∈[y]→x≡y y b y∈[b])
--       )
--       y∈xs
--     where
--     y∈xs : y ∈ (a ∷ b ∷ [])
--     y∈xs = subst (y ∈_) p (sort-∈ y (x ∷* [ y ]*) (L.inr (L.inl refl)))
-- 
--   is-sorted : List A -> Type _
--   is-sorted list = ∥ fiber sort list ∥₁
-- 
--   module _ (tail-sorted : ∀ x xs -> is-sorted (x ∷ xs) -> is-sorted xs) where
-- 
--     trans-≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
--     trans-≤ x y z x≤y y≤z =
--       {!   !}
--       where
--       least3 : least (x ∷* y ∷* z ∷* []*) ≡ just x
--       least3 =
--         least (x ∷* y ∷* z ∷* []*) ≡⟨⟩
--         {!   !}
-- 
--     ≤-isToset : IsToset _≤_
--     IsToset.is-set ≤-isToset = isSetA
--     IsToset.is-prop-valued ≤-isToset x y = isOfHLevelMaybe 0 isSetA _ _
--     IsToset.is-refl ≤-isToset = refl-≤
--     IsToset.is-trans ≤-isToset = trans-≤  
--     IsToset.is-antisym ≤-isToset = antisym-≤          
--     IsToset.is-strongly-connected ≤-isToset = total-≤      