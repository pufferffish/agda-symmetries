{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module Cubical.Structures.Set.CMon.SList.Sort.Base where

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

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

head-maybe : List A -> Maybe A
head-maybe [] = nothing
head-maybe (x ∷ xs) = just x

module Sort {A : Type ℓ} (isSetA : isSet A) (sort : SList A -> List A) where
  open Membership isSetA

  is-sorted : List A -> Type _
  is-sorted list = ∥ fiber sort list ∥₁

  is-section : Type _
  is-section = ∀ xs -> list→slist (sort xs) ≡ xs

  isProp-is-section : isProp is-section
  isProp-is-section = isPropΠ (λ _ -> trunc _ _)

  is-head-least : Type _
  is-head-least = ∀ x y xs -> is-sorted (x ∷ xs) -> y ∈ (x ∷ xs) -> is-sorted (x ∷ y ∷ [])

  is-tail-sort : Type _
  is-tail-sort = ∀ x xs -> is-sorted (x ∷ xs) -> is-sorted xs

  is-sort : Type _
  is-sort = is-head-least × is-tail-sort

  isProp-is-head-least : isProp is-head-least
  isProp-is-head-least = isPropΠ5 λ _ _ _ _ _ -> squash₁

  isProp-is-tail-sort : isProp is-tail-sort
  isProp-is-tail-sort = isPropΠ3 (λ _ _ _ -> squash₁)

  isProp-is-sort : isProp is-sort
  isProp-is-sort = isProp× isProp-is-head-least isProp-is-tail-sort

  is-sort-section : Type _
  is-sort-section = is-section × is-sort

  isProp-is-sort-section : isProp is-sort-section
  isProp-is-sort-section = isOfHLevelΣ 1 isProp-is-section (λ _ -> isProp-is-sort)

  module Section (sort≡ : is-section) where
    open Membership* isSetA

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

    sort-unique : ∀ xs -> is-sorted xs -> sort (list→slist xs) ≡ xs
    sort-unique xs = P.rec (isOfHLevelList 0 isSetA _ xs) λ (ys , p) ->
      sym (congS sort (sym (sort≡ ys) ∙ congS list→slist p)) ∙ p

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
