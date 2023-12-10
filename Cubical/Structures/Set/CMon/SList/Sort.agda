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

head-maybe : List A -> Maybe A
head-maybe [] = nothing
head-maybe (x ∷ xs) = just x

module Sort→Order (isSetA : isSet A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where

  isSetMaybeA : isSet (Maybe A)
  isSetMaybeA = isOfHLevelMaybe 0 isSetA

  private
    module 𝔖 = M.CMonSEq < SList A , slist-α > slist-sat
  
  open Membership isSetA
  open Membership* isSetA

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

    Prec : {X P : Type ℓ} -> isProp P -> ∥ X ∥₁ -> (X -> P) ->  P
    Prec x y z = P.rec x z y

    A≡ : A -> A -> hProp _
    A≡ x y = (x ≡ y) , isSetA x y

    just≡ : A -> A -> hProp _
    just≡ x y = (just x ≡ just y) , isSetMaybeA _ _

    maybe≡ : Maybe A -> Maybe A -> hProp _
    maybe≡ x y = (x ≡ y) , isSetMaybeA _ _

  sort-∈ : ∀ x xs -> x ∈* xs -> x ∈ sort xs
  sort-∈ x xs p = ∈*→∈ x (sort xs) (subst (x ∈*_) (sym (sort≡ xs)) p)

  sort-∈* : ∀ x xs -> x ∈ sort xs -> x ∈* xs
  sort-∈* x xs p = subst (x ∈*_) (sort≡ xs) (∈→∈* x (sort xs) p)

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

  least-choice-prop : ∀ x y -> hProp _
  least-choice-prop x y =
    (maybe≡ (least (x ∷* [ y ]*)) (just x))
    ⊔ (maybe≡ (least (x ∷* [ y ]*)) (just y))

  least-choice : ∀ x y -> ⟨ least-choice-prop x y ⟩
  least-choice x y with least (x ∷* [ y ]*) | inspect least (x ∷* [ y ]*)
  ... | nothing | [ p ]ᵢ =
    ⊥.rec (snotz (congS S.length (least-nothing (x ∷* [ y ]*) p)))
  ... | just z  | [ p ]ᵢ =
    ⊔-elim (A≡ z x) ((A≡ z y) ⊔ (⊥* , isProp⊥*)) (λ _ -> (just≡ z x) ⊔ (just≡ z y))
      (λ q -> L.inl (congS just q))
      (L.inr ∘ ⊔-elim (A≡ z y) (⊥* , isProp⊥*) (λ _ -> (just≡ z y)) (congS just) ⊥.rec*)
      (least-in z (x ∷* [ y ]*) p)

  _≤_ : A -> A -> Type _
  x ≤ y = least (x ∷* y ∷* []*) ≡ just x

  isProp-≤ : ∀ {a} {b} -> isProp (a ≤ b)
  isProp-≤  = isSetMaybeA _ _

  ≤-Prop : ∀ x y -> hProp _
  ≤-Prop x y = (x ≤ y) , isProp-≤

  refl-≤ : ∀ x -> x ≤ x
  refl-≤ x = Prec isProp-≤ (least-choice x x) (⊎.rec (idfun _) (idfun _))

  antisym-≤ : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y
  antisym-≤ x y p q = Prec (isSetA x y) (least-choice x y) $
    ⊎.rec
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
      ∎)

  least-removed : ∀ x y z -> least (x ∷* y ∷* [ z ]*) ≡ just x -> least (x ∷* [ z ]*) ≡ just x
  least-removed x y z p = {!   !}

  trans-≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
  trans-≤ x y z p q with least (x ∷* y ∷* [ z ]*) | inspect least (x ∷* y ∷* [ z ]*)
  ... | nothing | [ r ]ᵢ = ⊥.rec (snotz (congS S.length (least-nothing _ r)))
  ... | just w  | [ r ]ᵢ = least-removed x y z (r ∙ congS just lemma)
    where
    yzx : y ∷* z ∷* [ x ]* ≡ x ∷* y ∷* [ z ]*
    yzx =
      y ∷* z ∷* [ x ]* ≡⟨ congS (y ∷*_) (swap z x []*) ⟩
      y ∷* x ∷* [ z ]* ≡⟨ swap y x [ z ]* ⟩
      x ∷* y ∷* [ z ]* ∎
    zxy : z ∷* x ∷* [ y ]* ≡ x ∷* y ∷* [ z ]*
    zxy =
      z ∷* x ∷* [ y ]* ≡⟨ swap z x [ y ]* ⟩
      x ∷* z ∷* [ y ]* ≡⟨ congS (x ∷*_) (swap z y []*) ⟩
      x ∷* y ∷* [ z ]* ∎

    lemma-on-y : w ≡ y -> w ≡ x
    lemma-on-y w≡y =
      sym $ antisym-≤ x w (subst (x ≤_) (sym w≡y) p) $ least-removed w z x $
      least (w ∷* z ∷* [ x ]*) ≡⟨ congS (λ t -> least (t ∷* z ∷* [ x ]*)) w≡y ⟩
      least (y ∷* z ∷* [ x ]*) ≡⟨ congS least yzx ⟩
      least (x ∷* y ∷* [ z ]*) ≡⟨ r ⟩
      just w ∎

    lemma : w ≡ x
    lemma =
      ⊔-elim (A≡ w x) (∈*Prop w (y ∷* [ z ]*)) (λ _ -> A≡ w x)
        (λ w≡x -> w≡x)
        (⊔-elim (A≡ w y) (∈*Prop w [ z ]*) (λ _ -> A≡ w x)
          lemma-on-y
          (λ w∈[z] ->
            let w≡z = x∈[y]→x≡y w z w∈[z] in lemma-on-y $
            sym $ antisym-≤ y w (subst (y ≤_) (sym w≡z) q) $ least-removed w x y $
            least (w ∷* x ∷* [ y ]*) ≡⟨ congS (λ t -> least (t ∷* x ∷* [ y ]*)) w≡z ⟩
            least (z ∷* x ∷* [ y ]*) ≡⟨ congS least zxy ⟩
            least (x ∷* y ∷* [ z ]*) ≡⟨ r ⟩
            just w ∎
          )
        )
        (least-in w (x ∷* y ∷* [ z ]*) r)
    

  total-≤ : ∀ x y -> (x ≤ y) ⊔′ (y ≤ x)
  total-≤ x y = Prec squash₁ (least-choice x y) $ ⊎.rec
    L.inl
    (λ p -> L.inr $
      least (y ∷* [ x ]*) ≡⟨ congS least (swap y x []*) ⟩
      least (x ∷* [ y ]*) ≡⟨ p ⟩
      just y
    ∎)

  -- dec-≤ : ∀ x y -> (x ≤ y) ⊎ (¬(x ≤ y))
  -- dec-≤ x y = decRec inl inr ((discreteMaybe discreteA) (least (x ∷* y ∷* []*)) (just x))

  ≤-isToset : IsToset _≤_
  IsToset.is-set ≤-isToset = isSetA
  IsToset.is-prop-valued ≤-isToset x y = isOfHLevelMaybe 0 isSetA _ _
  IsToset.is-refl ≤-isToset = refl-≤
  IsToset.is-trans ≤-isToset = {!   !}
  IsToset.is-antisym ≤-isToset = antisym-≤
  IsToset.is-strongly-connected ≤-isToset = total-≤  