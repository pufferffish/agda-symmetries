{-# OPTIONS --cubical #-}

module FreeMon where

open import Cubical.Foundations.Everything
import Mon as M

data FreeMon (A : Type) : Type where
  η : (a : A) -> FreeMon A
  e : FreeMon A
  _⊕_ : FreeMon A -> FreeMon A -> FreeMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  trunc : isSet (FreeMon A)

freeMon : (A : Type) -> M.MonStruct (FreeMon A)
M.MonStruct.e (freeMon A) = e
M.MonStruct._⊕_ (freeMon A) = _⊕_
M.MonStruct.unitl (freeMon A) = unitl
M.MonStruct.unitr (freeMon A) = unitr
M.MonStruct.assocr (freeMon A) = assocr
M.MonStruct.trunc (freeMon A) = trunc

module _ {A B : Type} (M : M.MonStruct B) where
  module B = M.MonStruct M

  _♯ : (f : A -> B) -> FreeMon A -> B
  (f ♯) (η a) = f a
  (f ♯) e = B.e
  (f ♯) (m ⊕ n) = (f ♯) m B.⊕ (f ♯) n
  (f ♯) (unitl m i) = B.unitl ((f ♯) m) i
  (f ♯) (unitr m i) = B.unitr ((f ♯) m) i
  (f ♯) (assocr m n o i) = B.assocr ((f ♯) m) ((f ♯) n) ((f ♯) o) i
  (f ♯) (trunc m n p q i j) = B.trunc ((f ♯) m) ((f ♯) n) (cong (f ♯) p) (cong (f ♯) q) i j

  ♯-isMonHom : {f : A -> B} -> M.isMonHom (freeMon A) M (f ♯)
  M.isMonHom.f-e ♯-isMonHom = refl
  M.isMonHom.f-⊕ ♯-isMonHom m n = refl

  freeMonEquivLemma : (g : (FreeMon A -> B)) -> (x : FreeMon A) -> ((λ y -> g (η y)) ♯) x ≡ g x
  freeMonEquivLemma g (η a) = refl
  freeMonEquivLemma g e = {!   !}
  freeMonEquivLemma g (x ⊕ x₁) = {!   !}
  freeMonEquivLemma g (unitl x i) = {!   !}
  freeMonEquivLemma g (unitr x i) = {!   !}
  freeMonEquivLemma g (assocr x x₁ x₂ i) = {!   !}
  freeMonEquivLemma g (trunc x x₁ x₂ y i i₁) = {!   !}

  freeMonEquiv : isEquiv \f -> f ∘ η
  freeMonEquiv = isoToIsEquiv (iso (\f -> f ∘ η) _♯ (\f -> refl) (\f i x -> freeMonEquivLemma f x i))
  