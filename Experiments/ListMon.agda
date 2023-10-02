{-# OPTIONS --cubical #-}

module Experiments.ListMon where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
import Mon as M

data List (A : Type) : Type where
  [] : List A
  _∷_ : (a : A) -> List A -> List A
  trunc : isSet (List A)

module elimListSet {p : Level} {A : Type} (P : List A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : List A} -> P xs -> P (x ∷ xs))
                   (trunc* : {xs : List A} -> isSet (P xs))
                   where
  f : (xs : List A) -> P xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (\xs -> trunc* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module elimListProp {p : Level} {A : Type} (P : List A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : List A} -> P xs -> P (x ∷ xs))
                   (trunc* : {xs : List A} -> isProp (P xs))
                   where
  f : (xs : List A) -> P xs
  f = elimListSet.f P []* _∷*_ (isProp→isSet trunc*)

[_] : {A : Type} -> A -> List A
[ a ] = a ∷ []

_⊕_ : {A : Type} -> List A -> List A -> List A
[] ⊕ ys = ys
(x ∷ xs) ⊕ ys = x ∷ (xs ⊕ ys)
trunc xs ys p q i j ⊕ zs = trunc (xs ⊕ zs) (ys ⊕ zs) (cong (_⊕ zs) p) (cong (_⊕ zs) q) i j

unitl : {A : Type} -> ∀ (m : List A) -> [] ⊕ m ≡ m
unitl _ = refl

unitr : {A : Type} -> ∀ (m : List A) -> m ⊕ [] ≡ m
unitr =
  elimListProp.f _
    refl
    (\x p -> cong (x ∷_) p) 
    (trunc _ _)

assocr : {A : Type} -> ∀ (m n o : List A) -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
assocr =
  elimListProp.f _
    (λ _ _ -> refl)
    (λ x p n o -> cong (x ∷_) (p n o))
    (isPropΠ λ _ -> isPropΠ λ _ -> trunc _ _)

listMon : (A : Type) -> M.MonStruct (List A)
M.MonStruct.e (listMon _) = []
M.MonStruct._⊕_ (listMon _) = _⊕_
M.MonStruct.unitl (listMon _) = unitl
M.MonStruct.unitr (listMon _) = unitr
M.MonStruct.assocr (listMon _) = assocr
M.MonStruct.trunc (listMon _) = trunc

module _ {A B : Type} (M : M.MonStruct B) where
  module B = M.MonStruct M
  module _ (f : A -> B) where

    _♯ : List A -> B
    (_♯) [] = B.e
    (_♯) (x ∷ xs) = f x B.⊕ (_♯) xs
    (_♯) (trunc m n p q i j) = B.trunc ((_♯) m) ((_♯) n) (cong (_♯) p) (cong (_♯) q) i j

    _♯-isMonHom : M.isMonHom (listMon A) M _♯
    M.isMonHom.f-e _♯-isMonHom = refl
    M.isMonHom.f-⊕ _♯-isMonHom =
      elimListProp.f _
        (λ b -> sym (B.unitl (b ♯)))
        (λ x {xs} p b ->
          f x B.⊕ ((xs ⊕ b) ♯) ≡⟨ cong (f x B.⊕_) (p b) ⟩
          f x B.⊕ ((xs ♯) B.⊕ (b ♯)) ≡⟨ sym (B.assocr (f x) _ _) ⟩
          (f x B.⊕ (xs ♯)) B.⊕ (b ♯)
          ∎
        )
        (isPropΠ λ _ -> B.trunc _ _)
       
  private
    listMonEquivLemma : (f : List A -> B) -> M.isMonHom (listMon A) M f -> (x : List A) -> f x ≡ ((f ∘ [_]) ♯) x
    listMonEquivLemma f homMonWit = elimListProp.f _
      (M.isMonHom.f-e homMonWit)
      (λ x {xs} p ->
        f ([ x ] ⊕ xs) ≡⟨ M.isMonHom.f-⊕ homMonWit [ x ] xs ⟩
        f [ x ] B.⊕ f xs ≡⟨ cong (f [ x ] B.⊕_) p ⟩
        (f ∘ [_]) x B.⊕ ((f ∘ [_]) ♯) xs
        ∎)
      (B.trunc _ _)
    
    listMonEquivLemma-β : (f : List A -> B) -> M.isMonHom (listMon A) M f -> ((f ∘ [_]) ♯) ≡ f
    listMonEquivLemma-β f homMonWit i x = listMonEquivLemma f homMonWit x (~ i)

  listMonEquiv : M.MonHom (listMon A) M ≃ (A -> B)
  listMonEquiv = isoToEquiv
    ( iso
      (λ (f , ϕ) -> f ∘ [_])
      (λ f -> (f ♯) , (f ♯-isMonHom))
      (λ f i x -> B.unitr (f x) i)
      (λ (f , homMonWit) -> Σ≡Prop M.isMonHom-isProp (listMonEquivLemma-β f homMonWit))
    )

  listMonIsEquiv : isEquiv {A = M.MonHom (listMon A) M} (\(f , ϕ) -> f ∘ [_])
  listMonIsEquiv = listMonEquiv .snd
