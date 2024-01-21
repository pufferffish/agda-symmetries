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

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

head-maybe : List A -> Maybe A
head-maybe [] = nothing
head-maybe (x ∷ xs) = just x

module Sort {A : Type ℓ} (isSetA : isSet A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where
  open Membership isSetA

  is-sorted : List A -> Type _
  is-sorted list = ∥ fiber sort list ∥₁

  is-sort : Type _
  is-sort = ∀ x y xs -> is-sorted (x ∷ xs) -> y ∈ (x ∷ xs) -> is-sorted (x ∷ y ∷ [])

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

  private
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
    ... | no ¬x≤y = subst (_≤ y) (just-inj y x (congS head-maybe p)) (is-refl y)
    insert-≤ x y (z ∷ zs) ys p with y ≤? z
    ... | yes y≤z = lemma
      where
      lemma : x ≤ y
      lemma with x ≤? y
      ... | yes x≤y = x≤y
      ... | no ¬x≤y = subst (_≤ y) (just-inj y x (congS head-maybe p)) (is-refl y)
    ... | no ¬y≤z = lemma
      where
      lemma : x ≤ y
      lemma with x ≤? z
      ... | yes x≤z = subst (x ≤_) (just-inj z y (congS head-maybe (cons-inj₂ p))) x≤z
      ... | no ¬x≤z = ⊥.rec (¬x≤z (subst (_≤ z) (just-inj z x (congS head-maybe p)) (is-refl z)))

    not-total-impossible : ∀ {x y} -> ¬(x ≤ y) -> ¬(y ≤ x) -> ⊥
    not-total-impossible {x} {y} p q =
      P.rec isProp⊥ (⊎.rec p q) (is-strongly-connected x y)

  sort : SList A -> List A
  sort = Elim.f []
    (λ x xs -> insert x xs)
    (λ x y xs -> sort-eq x y xs)
    (λ _ -> isOfHLevelList 0 is-set)
    where
    case1 : ∀ {x y z zs} -> y ≤ z -> x ≤ z -> insert x (y ∷ z ∷ zs) ≡ insert y (x ∷ z ∷ zs)
    case1 {x} {y} {z} {zs} y≤z x≤z with x ≤? y | y ≤? x
    ... | yes x≤y | yes y≤x =
      cong₂ (λ u v -> (u ∷ v ∷ z ∷ zs)) x≡y (sym x≡y)
      where
      x≡y : x ≡ y
      x≡y = is-antisym x y x≤y y≤x
    ... | yes x≤y | no ¬y≤x = sym $
      x ∷ (insert y (z ∷ zs)) ≡⟨ congS (x ∷_) (insert-β-1 y z zs y≤z) ⟩
      x ∷ y ∷ z ∷ zs ∎
    ... | no ¬x≤y | yes y≤x =
      y ∷ (insert x (z ∷ zs)) ≡⟨ congS (y ∷_) (insert-β-1 x z zs x≤z) ⟩
      y ∷ x ∷ z ∷ zs ∎
    ... | no ¬x≤y | no ¬y≤x = ⊥.rec (not-total-impossible ¬x≤y ¬y≤x)
    case2 : ∀ {x y z zs} -> y ≤ z -> ¬(x ≤ z) -> insert x (y ∷ z ∷ zs) ≡ insert y (z ∷ insert x zs)
    case2 {x} {y} {z} {zs} y≤z ¬x≤z with x ≤? y
    ... | yes x≤y = ⊥.rec (¬x≤z (is-trans x y z x≤y y≤z))
    ... | no ¬x≤y =
      y ∷ (insert x (z ∷ zs)) ≡⟨ congS (y ∷_) (insert-β-2 x z zs ¬x≤z) ⟩
      y ∷ z ∷ insert x zs ≡⟨ sym (insert-β-1 y z _ y≤z) ⟩
      insert y (z ∷ insert x zs) ∎
    case3 : ∀ {x y z zs} -> ¬(y ≤ z) -> x ≤ z -> insert x (z ∷ insert y zs) ≡ insert y (x ∷ z ∷ zs)
    case3 {x} {y} {z} {zs} ¬y≤z x≤z with y ≤? x
    ... | yes y≤x = ⊥.rec (¬y≤z (is-trans y x z y≤x x≤z))
    ... | no ¬y≤x =
      insert x (z ∷ insert y zs) ≡⟨ insert-β-1 x z _ x≤z ⟩
      x ∷ z ∷ insert y zs ≡⟨ congS (x ∷_) (sym (insert-β-2 y z zs ¬y≤z)) ⟩
      x ∷ insert y (z ∷ zs) ∎

    sort-eq : ∀ x y xs -> insert x (insert y xs) ≡ insert y (insert x xs)
    sort-eq x y [] with x ≤? y | y ≤? x
    ... | yes x≤y | no ¬y≤x = refl
    ... | no ¬x≤y | yes y≤x = refl
    ... | no ¬x≤y | no ¬y≤x = ⊥.rec (not-total-impossible ¬x≤y ¬y≤x)
    ... | yes x≤y | yes y≤x =
      cong₂ (λ u v -> u ∷ v ∷ []) x≡y (sym x≡y)
      where
      x≡y : x ≡ y
      x≡y = is-antisym x y x≤y y≤x
    sort-eq x y (z ∷ zs) with y ≤? z | x ≤? z
    ... | yes y≤z | yes x≤z = case1 y≤z x≤z
    ... | yes y≤z | no ¬x≤z = case2 y≤z ¬x≤z
    ... | no ¬y≤z | yes x≤z = case3 ¬y≤z x≤z
    ... | no ¬y≤z | no ¬x≤z =
      insert x (z ∷ insert y zs) ≡⟨ insert-β-2 x z _ ¬x≤z ⟩
      z ∷ insert x (insert y zs) ≡⟨ congS (z ∷_) (sort-eq x y zs) ⟩
      z ∷ insert y (insert x zs) ≡⟨ sym (insert-β-2 y z _ ¬y≤z) ⟩
      insert y (z ∷ insert x zs) ∎

  private
    sort-membership : ∀ x xs -> x ∷* list→slist (sort xs) ≡ list→slist (sort (x ∷* xs))
    sort-membership x xs = {!   !}

  sort-is-permute : ∀ xs -> list→slist (sort xs) ≡ xs
  sort-is-permute = ElimProp.f (trunc _ _) refl lemma
    where
    lemma : ∀ x {xs} p -> list→slist (sort (x ∷* xs)) ≡ x ∷* xs
    lemma x {xs} p = sym $
      x ∷* xs ≡⟨ congS (x ∷*_) (sym p) ⟩
      x ∷* list→slist (sort xs) ≡⟨ sort-membership x xs ⟩
      list→slist (sort (x ∷* xs)) ∎

  open Sort is-set sort sort-is-permute

  private
    tail-is-sorted : ∀ x xs -> is-sorted (x ∷ xs) -> is-sorted xs
    tail-is-sorted x xs = P.rec squash₁ {!   !}
    
    sort→order-lemma : ∀ x y xs -> is-sorted (x ∷ y ∷ xs) -> x ≤ y
    sort→order-lemma x y xs = P.rec (is-prop-valued x y) (uncurry lemma)
      where
      lemma : ∀ ys p -> x ≤ y
      lemma ys p = insert-≤ x y (sort tail) xs (congS sort tail-proof ∙ p)
        where
        tail : SList A
        tail = {!   !}
        tail-proof : x ∷* y ∷* tail ≡ ys
        tail-proof = {!   !}

  sort→order : ∀ x y xs -> is-sorted (x ∷ xs) -> y ∈ (x ∷ xs) -> x ≤ y
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

  sort-is-sort : is-sort
  sort-is-sort x y xs p y∈xs =
    ∣ (x ∷* y ∷* []* , insert-β-1 x y [] (sort→order x y xs p y∈xs)) ∣₁

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

module Sort→Order (isSetA : isSet A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where

  isSetMaybeA : isSet (Maybe A)
  isSetMaybeA = isOfHLevelMaybe 0 isSetA

  isSetListA : isSet (List A)
  isSetListA = isOfHLevelList 0 isSetA

  private
    module 𝔖 = M.CMonSEq < SList A , slist-α > slist-sat
  
  open Membership isSetA
  open Membership* isSetA
  open Sort isSetA sort sort≡

  list→slist-η : ∀ xs -> (x : A) -> list→slist xs ≡ [ x ]* -> xs ≡ [ x ]
  list→slist-η [] x p = ⊥.rec (znots (congS S.length p))
  list→slist-η (x ∷ []) y p = congS [_] ([-]-inj {ϕ = isSetA} p)
  list→slist-η (x ∷ y ∷ xs) z p = ⊥.rec (snotz (injSuc (congS S.length p)))

  sort-length≡-α : ∀ (xs : List A) -> L.length xs ≡ S.length (list→slist xs)
  sort-length≡-α [] = refl
  sort-length≡-α (x ∷ xs) = congS suc (sort-length≡-α xs)

  sort-length≡ : ∀ xs -> L.length (sort xs) ≡ S.length xs
  sort-length≡ xs = sort-length≡-α (sort xs) ∙ congS S.length (sort≡ xs)

  length-0 : ∀ (xs : List A) -> L.length xs ≡ 0 -> xs ≡ []
  length-0 [] p = refl
  length-0 (x ∷ xs) p = ⊥.rec (snotz p)

  sort-[] : ∀ xs -> sort xs ≡ [] -> xs ≡ []*
  sort-[] xs p = sym (sort≡ xs) ∙ congS list→slist p

  sort-[]' : sort []* ≡ []
  sort-[]' = length-0 (sort []*) (sort-length≡ []*)

  sort-[-] : ∀ x -> sort [ x ]* ≡ [ x ]
  sort-[-] x = list→slist-η (sort [ x ]*) x (sort≡ [ x ]*)

  sort-∈ : ∀ x xs -> x ∈* xs -> x ∈ sort xs
  sort-∈ x xs p = ∈*→∈ x (sort xs) (subst (x ∈*_) (sym (sort≡ xs)) p)

  sort-∈* : ∀ x xs -> x ∈ sort xs -> x ∈* xs
  sort-∈* x xs p = subst (x ∈*_) (sort≡ xs) (∈→∈* x (sort xs) p)

  sort-choice-lemma : ∀ x -> sort (x ∷* x ∷* []*) ≡ x ∷ x ∷ []
  sort-choice-lemma x with sort (x ∷* x ∷* []*) | inspect sort (x ∷* x ∷* []*)
  ... | []                | [ p ]ᵢ = ⊥.rec (snotz (sym (sort-length≡ (x ∷* x ∷* []*)) ∙ congS L.length p))
  ... | x₁ ∷ []           | [ p ]ᵢ = ⊥.rec (snotz (injSuc (sym (sort-length≡ (x ∷* x ∷* []*)) ∙ congS L.length p)))
  ... | x₁ ∷ x₂ ∷ x₃ ∷ xs | [ p ]ᵢ = ⊥.rec (znots (injSuc (injSuc (sym (sort-length≡ (x ∷* x ∷* []*)) ∙ congS L.length p))))
  ... | a ∷ b ∷ [] | [ p ]ᵢ =
    P.rec (isOfHLevelList 0 isSetA _ _)
      (⊎.rec lemma1 (lemma1 ∘ x∈[y]→x≡y a x))
      (sort-∈* a (x ∷* x ∷* []*) (subst (a ∈_) (sym p) (x∈xs a [ b ])))
    where
    lemma2 : a ≡ x -> b ≡ x -> a ∷ b ∷ [] ≡ x ∷ x ∷ []
    lemma2 q r = cong₂ (λ u v -> u ∷ v ∷ []) q r
    lemma1 : a ≡ x -> a ∷ b ∷ [] ≡ x ∷ x ∷ []
    lemma1 q =
        P.rec (isOfHLevelList 0 isSetA _ _)
          (⊎.rec (lemma2 q) (lemma2 q ∘ x∈[y]→x≡y b x))
          (sort-∈* b (x ∷* x ∷* []*) (subst (b ∈_) (sym p) (L.inr (L.inl refl))))

  sort-choice : ∀ x y -> (sort (x ∷* y ∷* []*) ≡ x ∷ y ∷ []) ⊔′ (sort (x ∷* y ∷* []*) ≡ y ∷ x ∷ [])
  sort-choice x y with sort (x ∷* y ∷* []*) | inspect sort (x ∷* y ∷* []*) 
  ... | []                | [ p ]ᵢ = ⊥.rec (snotz (sym (sort-length≡ (x ∷* y ∷* []*)) ∙ congS L.length p))
  ... | x₁ ∷ []           | [ p ]ᵢ = ⊥.rec (snotz (injSuc (sym (sort-length≡ (x ∷* y ∷* []*)) ∙ congS L.length p)))
  ... | x₁ ∷ x₂ ∷ x₃ ∷ xs | [ p ]ᵢ = ⊥.rec (znots (injSuc (injSuc (sym (sort-length≡ (x ∷* y ∷* []*)) ∙ congS L.length p))))
  ... | a ∷ b ∷ [] | [ p ]ᵢ =
    P.rec squash₁
      (⊎.rec
        (λ x≡a -> P.rec squash₁
          (⊎.rec
            (λ y≡a -> L.inl (sym p ∙ subst (λ u -> sort (x ∷* [ u ]*) ≡ x ∷ u ∷ []) (x≡a ∙ sym y≡a) (sort-choice-lemma x)))
            (λ y∈[b] -> L.inl (cong₂ (λ u v → u ∷ v ∷ []) (sym x≡a) (sym (x∈[y]→x≡y y b y∈[b]))))
          )
          (subst (y ∈_) p (sort-∈ y (x ∷* y ∷* []*) (L.inr (L.inl refl))))
        )
        (λ x∈[b] -> P.rec squash₁
          (⊎.rec
            (λ y≡a -> L.inr (cong₂ (λ u v → u ∷ v ∷ []) (sym y≡a) (sym (x∈[y]→x≡y x b x∈[b]))))
            (λ y∈[b] ->
              let x≡y = (x∈[y]→x≡y x b x∈[b]) ∙ sym (x∈[y]→x≡y y b y∈[b])
              in L.inl (sym p ∙ subst (λ u -> sort (x ∷* [ u ]*) ≡ x ∷ u ∷ []) x≡y (sort-choice-lemma x))
            )
          )
          (subst (y ∈_) p (sort-∈ y (x ∷* y ∷* []*) (L.inr (L.inl refl))))
        )
      )
      (subst (x ∈_) p (sort-∈ x (x ∷* y ∷* []*) (L.inl refl)))


  least : SList A -> Maybe A
  least xs = head-maybe (sort xs)

  least-nothing : ∀ xs -> least xs ≡ nothing -> xs ≡ []*
  least-nothing xs p with sort xs | inspect sort xs
  ... | []     | [ q ]ᵢ = sort-[] xs q
  ... | y ∷ ys | [ q ]ᵢ = ⊥.rec (¬just≡nothing p)

  least-Σ : ∀ x xs -> least xs ≡ just x -> Σ[ ys ∈ List A ] (sort xs ≡ x ∷ ys)
  least-Σ x xs p with sort xs
  ... | []     = ⊥.rec (¬nothing≡just p)
  ... | y ∷ ys = ys , congS (_∷ ys) (just-inj y x p)

  least-in : ∀ x xs -> least xs ≡ just x -> x ∈* xs
  least-in x xs p =
    let (ys , q) = least-Σ x xs p
        x∷ys≡xs = congS list→slist (sym q) ∙ sort≡ xs
    in subst (x ∈*_) x∷ys≡xs (x∈*xs x (list→slist ys))

  least-choice : ∀ x y -> (least (x ∷* [ y ]*) ≡ just x) ⊔′ (least (x ∷* [ y ]*) ≡ just y)
  least-choice x y = P.rec squash₁
    (⊎.rec
      (L.inl ∘ congS head-maybe)
      (L.inr ∘ congS head-maybe)
    )
    (sort-choice x y)

  _≤_ : A -> A -> Type _
  x ≤ y = least (x ∷* y ∷* []*) ≡ just x

  isProp-≤ : ∀ {a} {b} -> isProp (a ≤ b)
  isProp-≤  = isSetMaybeA _ _

  ≤-Prop : ∀ x y -> hProp _
  ≤-Prop x y = (x ≤ y) , isProp-≤

  refl-≤ : ∀ x -> x ≤ x
  refl-≤ x = P.rec isProp-≤ (⊎.rec (idfun _) (idfun _)) (least-choice x x)

  antisym-≤ : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y
  antisym-≤ x y p q = P.rec (isSetA x y)
    (⊎.rec
      (λ xy -> just-inj x y $
        just x ≡⟨ sym xy ⟩
        least (x ∷* y ∷* []*) ≡⟨ congS least (swap x y []*) ⟩
        least (y ∷* x ∷* []*) ≡⟨ q ⟩
        just y
      ∎)
      (λ yx -> just-inj x y $
        just x ≡⟨ sym p ⟩
        least (x ∷* [ y ]*) ≡⟨ yx ⟩
        just y
      ∎))
     (least-choice x y)

  total-≤ : ∀ x y -> (x ≤ y) ⊔′ (y ≤ x)
  total-≤ x y = P.rec squash₁
    (⊎.rec
      L.inl
      (λ p -> L.inr $
        least (y ∷* [ x ]*) ≡⟨ congS least (swap y x []*) ⟩
        least (x ∷* [ y ]*) ≡⟨ p ⟩
        just y
      ∎))
    (least-choice x y)

  is-sorted→≤ : ∀ x y -> is-sorted (x ∷ y ∷ []) -> x ≤ y
  is-sorted→≤ x y = P.rec (isSetMaybeA _ _) λ (xs , p) ->
    congS head-maybe (congS sort (sym (sym (sort≡ xs) ∙ congS list→slist p)) ∙ p)

  module _ (sort-is-sort : is-sort) where
    trans-≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
    trans-≤ x y z x≤y y≤z with least (x ∷* y ∷* z ∷* []*) | inspect least (x ∷* y ∷* z ∷* []*)
    ... | nothing | [ p ]ᵢ = ⊥.rec (snotz (congS S.length (least-nothing _ p)))
    ... | just u | [ p ]ᵢ =
      P.rec (isSetMaybeA _ _)
        (⊎.rec case1 
          (P.rec (isSetMaybeA _ _)
            (⊎.rec case2 (case3 ∘ x∈[y]→x≡y _ _))
          )
        )
        (least-in u (x ∷* y ∷* z ∷* []*) p)
      where
      tail' : Σ[ xs ∈ List A ] u ∷ xs ≡ sort (x ∷* y ∷* z ∷* []*)
      tail' with sort (x ∷* y ∷* z ∷* []*)
      ... | [] = ⊥.rec (¬nothing≡just p)
      ... | v ∷ xs = xs , congS (_∷ xs) (just-inj _ _ (sym p))
      tail : List A
      tail = tail' .fst
      tail-proof : u ∷ tail ≡ sort (x ∷* y ∷* z ∷* []*)
      tail-proof = tail' .snd
      u∷tail-is-sorted : is-sorted (u ∷ tail)
      u∷tail-is-sorted = ∣ ((x ∷* y ∷* z ∷* []*) , sym tail-proof) ∣₁
      u-is-smallest : ∀ v -> v ∈* (x ∷* y ∷* z ∷* []*) -> u ≤ v
      u-is-smallest v q =
        is-sorted→≤ u v (sort-is-sort u v tail u∷tail-is-sorted (subst (v ∈_) (sym tail-proof) (sort-∈ v _ q)))
      case1 : u ≡ x -> x ≤ z
      case1 u≡x = subst (_≤ z) u≡x (u-is-smallest z (L.inr (L.inr (L.inl refl))))
      case2 : u ≡ y -> x ≤ z
      case2 u≡y = subst (_≤ z) (antisym-≤ y x y≤x x≤y) y≤z
        where
        y≤x : y ≤ x
        y≤x = subst (_≤ x) u≡y (u-is-smallest x (L.inl refl))
      case3 : u ≡ z -> x ≤ z
      case3 u≡z = subst (x ≤_) (antisym-≤ y z y≤z z≤y) x≤y
        where
        z≤y : z ≤ y
        z≤y = subst (_≤ y) u≡z (u-is-smallest y (L.inr (L.inl refl)))

    ≤-isToset : IsToset _≤_
    IsToset.is-set ≤-isToset = isSetA
    IsToset.is-prop-valued ≤-isToset x y = isOfHLevelMaybe 0 isSetA _ _
    IsToset.is-refl ≤-isToset = refl-≤
    IsToset.is-trans ≤-isToset = trans-≤ 
    IsToset.is-antisym ≤-isToset = antisym-≤               
    IsToset.is-strongly-connected ≤-isToset = total-≤      