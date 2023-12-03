{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Sort where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)
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

list→slist-Hom : structHom < List A , list-α > < SList A , slist-α >
list→slist-Hom = ListDef.Free.ext listDef trunc (M.cmonSatMon slist-sat) S.[_]

list→slist : List A -> SList A
list→slist = list→slist-Hom .fst

head-maybe : List A -> Maybe A
head-maybe [] = nothing
head-maybe (x ∷ xs) = just x

module Sort→Order (isSetA : isSet A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where

  isSetMaybeA : isSet (Maybe A)
  isSetMaybeA = isOfHLevelMaybe 0 isSetA

  private
    module 𝔖 = M.CMonSEq < SList A , slist-α > slist-sat
  
  open S.Membership isSetA

  private
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

    list→slist-[] : (xs : List A) -> list→slist xs ≡ []* -> xs ≡ []
    list→slist-[] [] p = refl
    list→slist-[] (x ∷ xs) p = ⊥.rec (snotz (congS S.length p))

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
  least-choice x y with least (x ∷* [ y ]*) | inspect least (x ∷* [ y ]*)
  ... | nothing | [ p ]ᵢ =
    ⊥.rec (snotz (congS S.length (least-nothing (x ∷* [ y ]*) p)))
  ... | just z  | [ p ]ᵢ =
    ⊔-elim z≡x (z≡y ⊔ (⊥* , isProp⊥*)) (λ _ -> want1 ⊔ want2)
      (λ q -> L.inl (congS just q))
      (L.inr ∘ ⊔-elim z≡y (⊥* , isProp⊥*) (λ _ -> want2) (congS just) ⊥.rec*)
      (least-in z (x ∷* [ y ]*) p)
    where
    z≡x : hProp _
    z≡x = (z ≡ x) , isSetA z x
    z≡y : hProp _
    z≡y = (z ≡ y) , isSetA z y
    want1 : hProp _
    want1 = (just z ≡ just x) , isSetMaybeA _ _
    want2 : hProp _
    want2 = (just z ≡ just y) , isSetMaybeA _ _

  -- _≤_ : A -> A -> Type _
  -- x ≤ y = least (x ∷* y ∷* []*) ≡ just x

  -- refl-≤ : ∀ x -> x ≤ x
  -- refl-≤ x = ⊎.rec (λ p -> p) (λ p -> p) (least-choice x x)

  -- trans-≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
  -- trans-≤ x y z p q = {!   !}

  -- antisym-≤ : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y
  -- antisym-≤ x y p q = ⊎.rec
  --   (λ xy -> just-inj x y $
  --     just x ≡⟨ sym xy ⟩
  --     least (x ∷* y ∷* []*) ≡⟨ congS least (swap x y []*) ⟩
  --     least (y ∷* x ∷* []*) ≡⟨ q ⟩
  --     just y
  --   ∎)
  --   (λ yx -> just-inj x y $
  --     just x ≡⟨ sym p ⟩
  --     least (x ∷* [ y ]*) ≡⟨ yx ⟩
  --     just y
  --   ∎)
  --   (least-choice x y)

  -- total-≤ : ∀ x y -> (x ≤ y) ⊎ (y ≤ x)
  -- total-≤ x y = ⊎.rec
  --   (λ p -> inl p)
  --   (λ p -> inr $
  --     least (y ∷* [ x ]*) ≡⟨ congS least (swap y x []*) ⟩
  --     least (x ∷* [ y ]*) ≡⟨ p ⟩
  --     just y
  --   ∎)
  --   (least-choice x y)

  -- dec-≤ : ∀ x y -> (x ≤ y) ⊎ (¬(x ≤ y))
  -- dec-≤ x y = decRec inl inr ((discreteMaybe discreteA) (least (x ∷* y ∷* []*)) (just x))

  -- ≤-isToset : IsToset _≤_
  -- IsToset.is-set ≤-isToset = isSetA
  -- IsToset.is-prop-valued ≤-isToset x y = isOfHLevelMaybe 0 isSetA _ _
  -- IsToset.is-refl ≤-isToset = refl-≤
  -- IsToset.is-trans ≤-isToset = trans-≤
  -- IsToset.is-antisym ≤-isToset = antisym-≤
  -- IsToset.is-strongly-connected ≤-isToset x y = ∣ total-≤ x y ∣₁ 