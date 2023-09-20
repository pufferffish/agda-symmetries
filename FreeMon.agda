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

  private
    freeMonEquivLemma : (f : FreeMon A -> B) -> M.isMonHom (freeMon A) M f -> (x : FreeMon A) -> f x ≡ ((f ∘ η) ♯) x
    freeMonEquivLemma f homMonWit (η a) = refl
    freeMonEquivLemma f homMonWit e = M.isMonHom.f-e homMonWit
    freeMonEquivLemma f homMonWit (x ⊕ y) =
      f (x ⊕ y) ≡⟨ M.isMonHom.f-⊕ homMonWit x y ⟩
      f x B.⊕ f y ≡⟨ cong (B._⊕ f y) (freeMonEquivLemma f homMonWit x) ⟩
      ((f ∘ η) ♯) x B.⊕ f y ≡⟨ cong (((f ∘ η) ♯) x B.⊕_) (freeMonEquivLemma f homMonWit y) ⟩
      ((f ∘ η) ♯) x B.⊕ ((f ∘ η) ♯) y
      ∎
    freeMonEquivLemma f homMonWit (unitl x i) j = {!   !}
    freeMonEquivLemma f homMonWit (unitr x i) = {!   !}
    freeMonEquivLemma f homMonWit (assocr x x₁ x₂ i) = {!   !}
    freeMonEquivLemma f homMonWit (trunc x x₁ x₂ y i i₁) = {!   !}

    freeMonEquivLemma-β : (f : FreeMon A -> B) -> M.isMonHom (freeMon A) M f -> ((f ∘ η) ♯) ≡ f
    freeMonEquivLemma-β f homMonWit i x = freeMonEquivLemma f homMonWit x (~ i)


  freeMonEquiv : M.MonHom (freeMon A) M ≃ (A -> B)
  freeMonEquiv = isoToEquiv (iso (\(f , ϕ) -> f ∘ η) (\f -> (f ♯) , (f ♯-isMonHom)) (\f -> refl) lemma)
    where
    lemma : (homMon : Σ (FreeMon A -> B) (M.isMonHom (freeMon A) M))
            -> ((fst homMon ∘ η) ♯ , (fst homMon ∘ η) ♯-isMonHom) ≡ homMon
    lemma = {!   !}
    -- lemma (f , homMonWit) i =
    --   let p = freeMonEquivLemma-β f homMonWit 
    --   in p i , transp (λ j -> M.isMonHom (freeMon A) M (p (~ j))) i homMonWit


  freeMonIsEquiv : isEquiv {A = M.MonHom (freeMon A) M} (\(f , ϕ) -> f ∘ η)
  freeMonIsEquiv = freeMonEquiv .snd
  