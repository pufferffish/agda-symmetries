{-# OPTIONS --cubical #-}

module ListMon where

open import Cubical.Foundations.Everything
import Mon as M

data List (A : Type) : Type where
  [] : List A
  _∷_ : (a : A) -> List A -> List A
  trunc : isSet (List A)

propPathList : {A : Type} {xs ys : List A} -> isProp (xs ≡ ys)
propPathList = trunc _ _

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
    propPathList

-- unitr [] = refl
-- unitr (x ∷ xs) = cong (x ∷_) (unitr xs)
-- unitr (trunc xs ys p q i j) k =
--   trunc (unitr xs k) (unitr ys k) (λ l -> unitr (p l) k) (λ l -> unitr (q l) k) i j

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
  module _♯ (f : A -> B) where

    _♯ : List A -> B
    (_♯) [] = B.e
    (_♯) (x ∷ xs) = f x B.⊕ (_♯) xs
    (_♯) (trunc m n p q i j) = B.trunc ((_♯) m) ((_♯) n) (cong (_♯) p) (cong (_♯) q) i j

    private
      ⊕-♯-β : (a b : List A) → ((a ⊕ b) ♯) ≡ ((a ♯) B.⊕ (b ♯))
      ⊕-♯-β = elimListProp.f {!!} {!!} {!!} {!!}

    _♯-isMonHom : M.isMonHom (listMon A) M (_♯)
    M.isMonHom.f-e _♯-isMonHom = refl
    M.isMonHom.f-⊕ _♯-isMonHom = {!!}

    -- _♯-isMonHom {f} = record
    --   { f-e = refl
    --   ; f-⊕ = lemma f
    --   }
    --   where
    --   lemma : (f : A -> B) -> (a b : List A) -> (_♯) (a ⊕ b) ≡ ((_♯) a B.⊕ (_♯) b)
    --   lemma f [] [] = sym (B.unitr B.e)
    --   lemma f [] (a ∷ b) = sym (B.unitl (f a B.⊕ (_♯) b))
    --   lemma f (a ∷ as) [] =
    --     f a B.⊕ (_♯) (as ⊕ []) ≡⟨ cong (λ x -> f a B.⊕ (_♯) x) (unitr as) ⟩
    --     f a B.⊕ (_♯) as ≡⟨ sym (B.unitr (f a B.⊕ (_♯) as)) ⟩
    --     (f a B.⊕ (_♯) as) B.⊕ B.e
    --     ∎
    --   lemma f (a ∷ as) (b ∷ bs) =
    --     f a B.⊕ (_♯) (as ⊕ (b ∷ bs)) ≡⟨ cong (f a B.⊕_) (lemma f as (b ∷ bs)) ⟩
    --     f a B.⊕ ((_♯) as B.⊕ (f b B.⊕ (_♯) bs)) ≡⟨ sym (B.assocr (f a) _ _) ⟩
    --     (f a B.⊕ (_♯) as) B.⊕ (f b B.⊕ (_♯) bs)
    --     ∎
    --   lemma f (trunc xs ys p q i j) b = {!   !}
    --   lemma f b (trunc xs ys p q i j) = {!   !}

    -- -- eta : A -> List A
