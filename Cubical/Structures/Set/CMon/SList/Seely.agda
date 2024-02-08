{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical.Structures.Set.CMon.SList.Seely where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
import Cubical.Data.List as L
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

module _ {ℓ} {A B : Type ℓ} where

  open SListDef.Free

  isSetSList× : isSet (SList A × SList B)
  isSetSList× = isSet× trunc trunc

  slist×-α : sig M.MonSig (SList A × SList B) -> (SList A × SList B)
  slist×-α (M.`e , i) = [] , []
  slist×-α (M.`⊕ , i) = (i fzero) .fst ++ (i fone) .fst , (i fzero) .snd ++ (i fone) .snd

  slist×-sat : < (SList A × SList B) , slist×-α > ⊨ M.CMonSEq
  slist×-sat (M.`mon M.`unitl) ρ = refl
  slist×-sat (M.`mon M.`unitr) ρ = ≡-× (slist-sat (M.`mon M.`unitr) (fst ∘ ρ)) ((slist-sat (M.`mon M.`unitr) (snd ∘ ρ)))
  slist×-sat (M.`mon M.`assocr) ρ = ≡-× (slist-sat (M.`mon M.`assocr) (fst ∘ ρ)) ((slist-sat (M.`mon M.`assocr) (snd ∘ ρ)))
  slist×-sat M.`comm ρ = ≡-× (slist-sat M.`comm (fst ∘ ρ)) ((slist-sat M.`comm (snd ∘ ρ)))

  f-η : A ⊎ B -> SList A × SList B
  f-η (inl x) = [ x ] , []
  f-η (inr x) = [] , [ x ]
  
  f-hom : structHom < SList (A ⊎ B) , slist-α > < (SList A × SList B) , slist×-α >
  f-hom = ext slistDef isSetSList× slist×-sat f-η
  
  f : SList (A ⊎ B) -> SList A × SList B
  f = f-hom .fst

  mmap : ∀ {X Y : Type ℓ} -> (X -> Y) -> SList X -> SList Y
  mmap f = ext slistDef trunc slist-sat ([_] ∘ f) .fst

  mmap-++ : ∀ {X Y : Type ℓ} -> ∀ f xs ys -> mmap {X = X} {Y = Y} f (xs ++ ys) ≡ mmap f xs ++ mmap f ys 
  mmap-++ f xs ys = sym (ext slistDef trunc slist-sat ([_] ∘ f) .snd M.`⊕ ⟪ xs ⨾ ys ⟫)

  mmap-∷ : ∀ {X Y : Type ℓ} -> ∀ f x xs -> mmap {X = X} {Y = Y} f (x ∷ xs) ≡ f x ∷ mmap f xs 
  mmap-∷ f x xs = mmap-++ f [ x ] xs

  g : SList A × SList B -> SList (A ⊎ B)
  g (as , bs) = mmap inl as ++ mmap inr bs

  g-++ : ∀ xs ys -> g xs ++ g ys ≡ g (xs .fst ++ ys .fst , xs .snd ++ ys .snd)
  g-++ (as , bs) (cs , ds) = sym $
      g (as ++ cs , bs ++ ds)
    ≡⟨ cong (_++ mmap inr (bs ++ ds)) (mmap-++ inl as cs) ⟩
      (mmap inl as ++ mmap inl cs) ++ (mmap inr (bs ++ ds))
    ≡⟨ cong ((mmap inl as ++ mmap inl cs) ++_) (mmap-++ inr bs ds) ⟩
      (mmap inl as ++ mmap inl cs) ++ (mmap inr bs ++ mmap inr ds)
    ≡⟨ assoc-++ (mmap inl as ++ mmap inl cs) (mmap inr bs) (mmap inr ds) ⟩
      ((mmap inl as ++ mmap inl cs) ++ mmap inr bs) ++ mmap inr ds
    ≡⟨ cong (_++ mmap inr ds) (sym (assoc-++ (mmap inl as) (mmap inl cs) (mmap inr bs))) ⟩
      (mmap inl as ++ (mmap inl cs ++ mmap inr bs)) ++ mmap inr ds
    ≡⟨ cong (λ z → (mmap inl as ++ z) ++ mmap inr ds) (comm-++ (mmap inl cs) (mmap inr bs)) ⟩
      (mmap inl as ++ (mmap inr bs ++ mmap inl cs)) ++ mmap inr ds
    ≡⟨ cong (_++ mmap inr ds) (assoc-++ (mmap inl as) (mmap inr bs) (mmap inl cs)) ⟩
      ((mmap inl as ++ mmap inr bs) ++ mmap inl cs) ++ mmap inr ds
    ≡⟨ sym (assoc-++ (mmap inl as ++ mmap inr bs) (mmap inl cs) (mmap inr ds)) ⟩
      (mmap inl as ++ mmap inr bs) ++ (mmap inl cs ++ mmap inr ds)
    ≡⟨⟩
      g (as , bs) ++ g (cs , ds)
    ∎

  g-hom : structHom < (SList A × SList B) , slist×-α > < SList (A ⊎ B) , slist-α > 
  g-hom = g , g-is-hom
    where
    g-is-hom : structIsHom < SList A × SList B , slist×-α > < SList (A ⊎ B) , slist-α > g
    g-is-hom M.`e i = refl
    g-is-hom M.`⊕ i = g-++ (i fzero) (i fone)

  module _ {ℓ} {X : Type ℓ} (h : structHom < SList X , slist-α > < SList X , slist-α >) (h-η : ∀ x -> h .fst [ x ] ≡ [ x ]) where
    univ-htpy : ∀ xs -> h .fst xs ≡ xs
    univ-htpy xs = h~η♯ xs ∙ η♯~id xs
      where
      h~η♯ : ∀ xs -> h .fst xs ≡ ext slistDef trunc slist-sat [_] .fst xs
      h~η♯ = ElimProp.f (trunc _ _) (sym (h .snd M.`e ⟪⟫)) λ x {xs} p ->
        h .fst (x ∷ xs) ≡⟨ sym (h .snd M.`⊕ ⟪ [ x ] ⨾ xs ⟫) ⟩
        h .fst [ x ] ++ h .fst xs ≡⟨ congS (_++ h .fst xs) (h-η x) ⟩
        x ∷ h .fst xs ≡⟨ congS (x ∷_) p ⟩
        x ∷ ext slistDef trunc slist-sat [_] .fst xs ∎
      η♯~id : ∀ xs -> ext slistDef trunc slist-sat [_] .fst xs ≡ xs
      η♯~id xs = congS (λ h -> h .fst xs) (ext-β slistDef trunc slist-sat (idHom < SList X , slist-α >))
  
  g-f : ∀ xs -> g (f xs) ≡ xs
  g-f = univ-htpy (structHom∘ _ _ < SList (A ⊎ B) , slist-α > g-hom f-hom) lemma
    where
    lemma : ∀ x -> g (f [ x ]) ≡ [ x ]
    lemma (inl x) = refl
    lemma (inr x) = refl

  f-mmap-inl : ∀ as -> f (mmap inl as) ≡ (as , [])
  f-mmap-inl = ElimProp.f (isSetSList× _ _) refl λ x {xs} p ->
    f (mmap inl (x ∷ xs)) ≡⟨ cong f (mmap-∷ inl x xs) ⟩
    f (inl x ∷ mmap inl xs) ≡⟨ sym (f-hom .snd M.`⊕ ⟪ [ inl x ] ⨾ mmap inl xs ⟫) ⟩
    x ∷ f (mmap inl xs) .fst , f (mmap inl xs) .snd ≡⟨ congS (λ z -> x ∷ z .fst , z .snd) p ⟩
    x ∷ xs , [] ∎

  f-mmap-inr : ∀ as -> f (mmap inr as) ≡ ([] , as)
  f-mmap-inr = ElimProp.f (isSetSList× _ _) refl λ x {xs} p ->
    f (mmap inr (x ∷ xs)) ≡⟨ cong f (mmap-∷ inr x xs) ⟩
    f (inr x ∷ mmap inr xs) ≡⟨ sym (f-hom .snd M.`⊕ ⟪ [ inr x ] ⨾ mmap inr xs ⟫) ⟩
    f (mmap inr xs) .fst , x ∷ f (mmap inr xs) .snd ≡⟨ congS (λ z -> z .fst , x ∷ z .snd) p ⟩
    [] , x ∷ xs ∎

  f-g : ∀ xs -> f (g xs) ≡ xs
  f-g (as , bs) =
      f (g (as , bs))
    ≡⟨ sym (f-hom .snd M.`⊕ ⟪ mmap inl as ⨾ mmap inr bs ⟫) ⟩
      (f (mmap inl as) .fst ++ f (mmap inr bs) .fst) , (f (mmap inl as) .snd ++ f (mmap inr bs) .snd)
    ≡⟨ congS (λ z -> (z .fst ++ f (mmap inr bs) .fst) , (z .snd ++ f (mmap inr bs) .snd)) (f-mmap-inl as) ⟩
      as ++ f (mmap inr bs) .fst , [] ++ f (mmap inr bs) .snd
    ≡⟨ congS (λ z -> as ++ z .fst , [] ++ z .snd) (f-mmap-inr bs) ⟩
      as ++ [] , bs
    ≡⟨ congS (λ zs -> zs , bs) (unitr-++ as) ⟩
      as , bs ∎

  seely : SList (A ⊎ B) ≃ SList A × SList B
  seely = isoToEquiv (iso f g f-g g-f)