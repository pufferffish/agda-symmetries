{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical.Structures.Set.CMon.SList.Membership where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Sum as ⊎

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List

open import Cubical.Structures.Set.CMon.SList.Base as SList

private
  variable
    ℓ : Level
    A : Type ℓ

list→slist-Hom : structHom < L.List A , list-α > < SList A , slist-α >
list→slist-Hom = ListDef.Free.ext listDef trunc (M.cmonSatMon slist-sat) [_]

list→slist : L.List A -> SList A
list→slist = list→slist-Hom .fst

module Membership* {ℓ} {A : Type ℓ} (isSetA : isSet A) where
  open SList.Free {A = A} isSetHProp (M.⊔-MonStr-CMonSEq ℓ)
  
  ∈*Prop : A -> SList A -> hProp ℓ 
  ∈*Prop x = (λ y -> (x ≡ y) , isSetA x y) ♯

  _∈*_ : A -> SList A -> Type ℓ
  x ∈* xs = ∈*Prop x xs .fst
  
  isProp-∈* : (x : A) -> (xs : SList A) -> isProp (x ∈* xs)
  isProp-∈* x xs = (∈*Prop x xs) .snd
  
  x∈*xs : ∀ x xs -> x ∈* (x ∷ xs)
  x∈*xs x xs = L.inl refl

  x∈*[x] : ∀ x -> x ∈* [ x ]
  x∈*[x] x = x∈*xs x []

  ∈*-∷ : ∀ x y xs -> x ∈* xs -> x ∈* (y ∷ xs)
  ∈*-∷ x y xs p = L.inr p

  ∈*-++ : ∀ x xs ys -> x ∈* ys -> x ∈* (xs ++ ys)
  ∈*-++ x xs ys p =
    ElimProp.f {B = λ zs -> x ∈* (zs ++ ys)} (λ {zs} -> isProp-∈* x (zs ++ ys)) p
      (λ a {zs} q -> ∈*-∷ x a (zs ++ ys) q)
      xs

  ¬∈*[] : ∀ x -> (x ∈* []) -> ⊥.⊥
  ¬∈*[] x = ⊥.rec*

  x∈*[y]→x≡y : ∀ x y -> x ∈* [ y ] -> x ≡ y
  x∈*[y]→x≡y x y = P.rec (isSetA x y) $ ⊎.rec (idfun _) ⊥.rec*

  open Membership isSetA

  ∈→∈* : ∀ x xs -> x ∈ xs -> x ∈* (list→slist xs)
  ∈→∈* x (y L.∷ ys) = P.rec
    (isProp-∈* x (list→slist (y L.∷ ys)))
    (⊎.rec L.inl (L.inr ∘ ∈→∈* x ys))

  ∈*→∈ : ∀ x xs -> x ∈* (list→slist xs) -> x ∈ xs
  ∈*→∈ x (y L.∷ ys) = P.rec
    (isProp-∈ x (y L.∷ ys))
    (⊎.rec L.inl (L.inr ∘ ∈*→∈ x ys))