{-# OPTIONS --cubical #-}

module ListMon where

open import Cubical.Foundations.Everything
import Mon as M

data List (A : Type) : Type where
  [] : List A
  _∷_ : (a : A) -> List A -> List A
  trunc : isSet (List A)

_⊕_ : {A : Type} -> List A -> List A -> List A
[] ⊕ ys = ys
(x ∷ xs) ⊕ ys = x ∷ (xs ⊕ ys)
trunc xs ys x y i j ⊕ zs = trunc (xs ⊕ zs) (ys ⊕ zs) (cong (_⊕ zs) x) (cong (_⊕ zs) y) i j

unitl : {A : Type} -> ∀ (m : List A) -> [] ⊕ m ≡ m
unitl _ = refl

unitr : {A : Type} -> ∀ (m : List A) -> m ⊕ [] ≡ m
unitr [] = refl
unitr (x ∷ xs) = cong (x ∷_) (unitr xs)
unitr (trunc xs ys p q i j) k =
  trunc (unitr xs k) (unitr ys k) (λ l -> unitr (p l) k) (λ l -> unitr (q l) k) i j

assocr : {A : Type} -> ∀ (m n o : List A) -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
assocr [] n o = refl
assocr (x ∷ xs) n o = cong (x ∷_) (assocr xs n o)
assocr (trunc xs ys p q i j) n o k =
  trunc (assocr xs n o k) (assocr ys n o k) (λ l -> assocr (p l) n o k) (λ l -> assocr (q l) n o k) i j

listMon : {A : Type} -> M.MonStruct (List A)
listMon = record
  { e = []
  ; _⊕_ = _⊕_
  ; unitl = unitl
  ; unitr = unitr
  ; assocr = assocr
  ; trunc = trunc
  } 