{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.Mon.List.Combinatorics where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Sum as ⊎

open import Cubical.Structures.Set.Mon.List

private
  variable
    ℓ : Level
    A B : Type ℓ

module _ {ℓ} {A B : Type ℓ} (isSetA : isSet A) (isSetB : isSet B) where

  open ListDef.Free

  isSetListA : isSet (List A)
  isSetListA = isOfHLevelList 0 isSetA

  isSetListB : isSet (List B)
  isSetListB = isOfHLevelList 0 isSetB

  isSetList× : isSet (List A × List B)
  isSetList× = isSet× isSetListA isSetListB

  isSetList+ : isSet (List A ⊎ List B)
  isSetList+ = isSet⊎ isSetListA isSetListB

  list+-⊕ : (List A ⊎ List B) -> (List A ⊎ List B) -> (List A ⊎ List B)
  list+-⊕ (inl xs) (inl ys) = inl (xs ++ ys)
  list+-⊕ (inl xs) (inr ys) = inr ys
  list+-⊕ (inr xs) (inl ys) = inr xs
  list+-⊕ (inr xs) (inr ys) = inr (xs ++ ys)

  list+-α : sig M.MonSig (List A ⊎ List B) -> (List A ⊎ List B)
  list+-α (M.`e , i) = inl []
  list+-α (M.`⊕ , i) = list+-⊕ (i fzero) (i fone)

  list+-sat : < (List A ⊎ List B) , list+-α > ⊨ M.MonSEq
  list+-sat M.`unitl ρ with ρ fzero
  ... | inl _ = refl
  ... | inr _ = refl
  list+-sat M.`unitr ρ with ρ fzero
  ... | inl xs = congS inl (++-unit-r xs)
  ... | inr xs = refl
  list+-sat M.`assocr ρ with ρ fzero | ρ fone | ρ ftwo
  ... | inl xs | inl ys | inl zs = congS inl (++-assoc xs ys zs)
  ... | inl xs | inl ys | inr zs = refl
  ... | inl xs | inr ys | inl zs = refl
  ... | inl xs | inr ys | inr zs = refl
  ... | inr xs | inl ys | inl zs = refl
  ... | inr xs | inl ys | inr zs = refl
  ... | inr xs | inr ys | inl zs = refl
  ... | inr xs | inr ys | inr zs = congS inr (++-assoc xs ys zs)

  f-η : A ⊎ B -> List A ⊎ List B
  f-η (inl x) = inl [ x ]
  f-η (inr x) = inr [ x ]

  -- f-hom : structHom < List (A ⊎ B) , list-α > < (List A ⊎ List B) , list+-α >
  -- f-hom = f , {!   !}

  f-hom : structHom < List (A ⊎ B) , list-α > < (List A ⊎ List B) , list+-α >
  f-hom = ext listDef isSetList+ list+-sat f-η

  f : List (A ⊎ B) -> List A ⊎ List B
  f = f-hom .fst

  module ListMap {Y : Type ℓ} (isSetY : isSet Y) where
    mmap : ∀ {X : Type ℓ} -> (X -> Y) -> List X -> List Y
    mmap f = ext listDef (isOfHLevelList 0 isSetY) list-sat ([_] ∘ f) .fst

    mmap-++ : ∀ {X} f xs ys -> mmap {X = X} f (xs ++ ys) ≡ mmap f xs ++ mmap f ys
    mmap-++ f xs ys = sym $
      ext listDef (isOfHLevelList 0 isSetY) list-sat ([_] ∘ f) .snd M.`⊕ ⟪ xs ⨾ ys ⟫

  open ListMap (isSet⊎ isSetA isSetB)

  g : List A ⊎ List B -> List (A ⊎ B)
  g (inl xs) = mmap inl xs
  g (inr xs) = mmap inr xs

  g-f : ∀ xs -> g (f xs) ≡ xs
  g-f [] = refl
  g-f (x ∷ xs) = {!   !}

  f-g : ∀ xs -> f (g xs) ≡ xs
  f-g (inl []) = refl
  f-g (inl (x ∷ xs)) =
    f (mmap inl (x ∷ xs)) ≡⟨ congS f (mmap-++ inl [ x ] xs) ⟩
    f (inl x ∷ mmap inl xs) ≡⟨ sym (f-hom .snd M.`⊕ ⟪ [ inl x ] ⨾ mmap inl xs ⟫) ⟩
    list+-⊕ (inl [ x ]) (f (mmap inl xs)) ≡⟨ congS (list+-⊕ (inl [ x ])) (f-g (inl xs)) ⟩
    inl (x ∷ xs) ∎
  f-g (inr []) = {! refl  !}
  f-g (inr (x ∷ xs)) = {!   !}

  -- g-++ : ∀ xs ys -> g xs ++ g ys ≡ g (list+-⊕ xs ys)
  -- g-++ (inl xs) (inl ys) = mmap-++ inl xs ys
  -- g-++ (inr xs) (inr ys) = mmap-++ inr xs ys
  -- g-++ (inl xs) (inr ys) = {!   !}
  -- g-++ (inr xs) (inl ys) = {!   !}

  -- g-hom : structHom < (List A ⊎ List B) , list+-α > < List (A ⊎ B) , list-α >
  -- g-hom = g , g-is-hom
  --   where
  --   g-is-hom : structIsHom < List A ⊎ List B , list+-α > < List (A ⊎ B) , list-α > g
  --   g-is-hom M.`e i = refl
  --   g-is-hom M.`⊕ i = g-++ (i fzero) (i fone)



