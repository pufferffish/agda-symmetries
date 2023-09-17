{-# OPTIONS --cubical #-}

module ListMon where

open import Cubical.Foundations.Everything
import Mon as M

data List (A : Type) : Type where
  [] : List A
  _∷_ : (a : A) -> List A -> List A
  trunc : isSet (List A)

[_] : {A : Type} -> A -> List A
[ a ] = a ∷ []

_⊕_ : {A : Type} -> List A -> List A -> List A
[] ⊕ ys = ys
(x ∷ xs) ⊕ ys = x ∷ (xs ⊕ ys)
trunc xs ys p q i j ⊕ zs = trunc (xs ⊕ zs) (ys ⊕ zs) (cong (_⊕ zs) p) (cong (_⊕ zs) q) i j

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

listMon : (A : Type) -> M.MonStruct (List A)
listMon _ = record
  { e = []
  ; _⊕_ = _⊕_
  ; unitl = unitl
  ; unitr = unitr
  ; assocr = assocr
  ; trunc = trunc
  } 

module _ {A B : Type} (M : M.MonStruct B) where
  module B = M.MonStruct M

  _♯ : (f : A -> B) -> List A -> B
  (f ♯) [] = B.e
  (f ♯) (x ∷ xs) = f x B.⊕ (f ♯) xs
  (f ♯) (trunc m n p q i j) = B.trunc ((f ♯) m) ((f ♯) n) (cong (f ♯) p) (cong (f ♯) q) i j

  ♯-isMonHom : {f : A -> B} -> M.isMonHom (listMon A) M (f ♯)
  ♯-isMonHom {f} = record
    { f-e = refl
    ; f-⊕ = lemma f
    }
    where
    lemma : (f : A -> B) -> (a b : List A) -> (f ♯) (a ⊕ b) ≡ ((f ♯) a B.⊕ (f ♯) b)
    lemma f [] [] i = (B.unitr B.e) (~ i)
    lemma f [] (a ∷ b) i = (B.unitl (f a B.⊕ (f ♯) b)) (~ i)
    lemma f (a ∷ as) [] =
      f a B.⊕ (f ♯) (as ⊕ []) ≡⟨ cong (λ x -> f a B.⊕ (f ♯) x) (unitr as) ⟩ 
      f a B.⊕ (f ♯) as ≡⟨ sym (B.unitr (f a B.⊕ (f ♯) as)) ⟩
      (f a B.⊕ (f ♯) as) B.⊕ B.e
      ∎
    lemma f (a ∷ as) (b ∷ bs) =
      f a B.⊕ (f ♯) (as ⊕ (b ∷ bs)) ≡⟨ cong (f a B.⊕_) (lemma f as (b ∷ bs)) ⟩
      f a B.⊕ ((f ♯) as B.⊕ (f b B.⊕ (f ♯) bs)) ≡⟨ sym (B.assocr (f a) _ _) ⟩
      (f a B.⊕ (f ♯) as) B.⊕ (f b B.⊕ (f ♯) bs) 
      ∎
    lemma f (trunc xs ys p q i j) b = {!   !}
    lemma f b (trunc xs ys p q i j) = {!   !}

  listMonEquiv : isEquiv \f -> (f ♯) ∘ [_]
  listMonEquiv = isoToIsEquiv (iso {!   !} {!   !} {!   !} {!   !})

   