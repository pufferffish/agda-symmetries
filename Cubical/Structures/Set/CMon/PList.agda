{-# OPTIONS --cubical #-}

-- Taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.PList where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List as L
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients as Q


data Perm {ℓ : Level} {A : Type ℓ} : List A -> List A -> Type ℓ where
  perm-refl : ∀ {xs} -> Perm xs xs
  perm-swap : ∀ {x y xs ys zs} -> Perm (xs ++ x ∷ y ∷ ys) zs -> Perm (xs ++ y ∷ x ∷ ys) zs 

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

map++ : {f : A -> B} (xs : List A) {ys : List A} -> L.map f (xs ++ ys) ≡ L.map f xs ++ L.map f ys
map++ [] = refl
map++ (x ∷ xs) = cong (_ ∷_) (map++ xs)

infixr 30 _∙ₚ_
_∙ₚ_ : ∀ {xs ys zs} -> Perm xs ys -> Perm ys zs -> Perm {A = A} xs zs
perm-refl ∙ₚ q = q
(perm-swap p) ∙ₚ q = perm-swap (p ∙ₚ q)

perm-sym : ∀ {xs ys} -> Perm xs ys -> Perm {A = A} ys xs
perm-sym perm-refl = perm-refl
perm-sym (perm-swap p) = perm-sym p ∙ₚ perm-swap perm-refl

perm-subst : ∀ {xs ys} -> xs ≡ ys -> Perm {A = A} xs ys
perm-subst {xs = xs} p = subst (Perm xs) p perm-refl

perm-∷ : ∀ {x xs ys} -> Perm xs ys -> Perm {A = A} (x ∷ xs) (x ∷ ys)
perm-∷ perm-refl = perm-refl
perm-∷ {x = x} (perm-swap {xs = xs} p) = perm-swap {xs = x ∷ xs} (perm-∷ p)

perm-prepend : (xs : List A) {ys zs : List A} -> Perm ys zs -> Perm (xs ++ ys) (xs ++ zs)
perm-prepend [] p = p
perm-prepend (x ∷ xs) p = perm-∷ (perm-prepend xs p)

perm-append : {xs ys zs : List A} -> Perm xs ys -> Perm (xs ++ zs) (ys ++ zs)
perm-append perm-refl = perm-refl
perm-append (perm-swap {xs = xs} p) =
  perm-subst (++-assoc xs _ _) ∙ₚ perm-swap (perm-subst (sym (++-assoc xs _ _)) ∙ₚ perm-append p)

perm-movehead : (x : A) (xs : List A) {ys : List A} -> Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
perm-movehead x [] = perm-refl
perm-movehead x (y ∷ xs) = perm-swap {xs = []} (perm-∷ (perm-movehead x xs))

perm-comm : (xs ys : List A) -> Perm (xs ++ ys) (ys ++ xs)
perm-comm xs [] = perm-subst (++-unit-r xs)
perm-comm xs (y ∷ ys) = perm-sym (perm-movehead y xs {ys = ys}) ∙ₚ perm-∷ (perm-comm xs ys)

perm-map : (f : A -> B) {xs ys : List A} -> Perm xs ys -> Perm (L.map f xs) (L.map f ys)
perm-map f perm-refl = perm-refl
perm-map f (perm-swap {xs = xs} p) = perm-subst (map++ xs) ∙ₚ perm-swap (perm-subst (sym (map++ xs)) ∙ₚ perm-map f p)

PList : Type ℓ -> Type ℓ
PList A = List A / Perm

_⊕_ : PList A -> PList A -> PList A
_⊕_ = Q.rec2 squash/
  (λ xs ys -> Q.[ xs ++ ys ])
  (λ as bs cs p -> eq/ (as ++ cs) (bs ++ cs) (perm-append p))
  (λ as bs cs p -> eq/ (as ++ bs) (as ++ cs) (perm-prepend as p))