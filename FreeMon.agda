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
  module _ (f : A -> B) where

    _♯ : FreeMon A -> B
    (_♯) (η a) = f a
    (_♯) e = B.e
    (_♯) (m ⊕ n) = (_♯) m B.⊕ (_♯) n
    (_♯) (unitl m i) = B.unitl ((_♯) m) i
    (_♯) (unitr m i) = B.unitr ((_♯) m) i
    (_♯) (assocr m n o i) = B.assocr ((_♯) m) ((_♯) n) ((_♯) o) i
    (_♯) (trunc m n p q i j) = B.trunc ((_♯) m) ((_♯) n) (cong (_♯) p) (cong (_♯) q) i j

    _♯-isMonHom : M.isMonHom (freeMon A) M _♯
    M.isMonHom.f-e _♯-isMonHom = refl
    M.isMonHom.f-⊕ _♯-isMonHom m n = refl

  freeMonEquiv : M.MonHom (freeMon A) M ≃ (A -> B)
  freeMonEquiv = isoToEquiv (iso (\(f , ϕ) -> f ∘ η) (\f -> (f ♯) , (f ♯-isMonHom)) (\f -> refl) {!!})

  freeMonIsEquiv : isEquiv {A = M.MonHom (freeMon A) M} (\(f , ϕ) -> f ∘ η)
  freeMonIsEquiv = freeMonEquiv .snd
