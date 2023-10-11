{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.SList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma

infixr 20 _∷_

data SList {a} (A : Type a) : Type a where
  [] : SList A
  _∷_ : (a : A) -> (as : SList A) -> SList A
  swap : (a b : A) (cs : SList A)
      -> a ∷ b ∷ cs ≡ b ∷ a ∷ cs
  isSetSList : isSet (SList A)

pattern [_] a = a ∷ []

module elimSListSet {ℓ p : Level} {A : Type ℓ} (P : SList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : SList A} -> P xs -> P (x ∷ xs))
                   (swap* : (a b : A) -> {cs : SList A}
                            -> (cs* : P cs)
                            -> PathP (λ i -> P (swap a b cs i)) (a ∷* (b ∷* cs*)) (b ∷* (a ∷* cs*))
                   )
                   (isSetSList* : {xs : SList A} -> isSet (P xs))
                   where
  f : (xs : SList A) -> P xs
  f [] = []*
  f (a ∷ xs) = a ∷* f xs
  f (swap a b xs i) = swap* a b (f xs) i
  f (isSetSList xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (\xs -> isSetSList* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (isSetSList xs ys p q) i j

module elimSListProp {ℓ p : Level} {A : Type ℓ} (P : SList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : SList A} -> P xs -> P (x ∷ xs))
                   (isSetSList* : {xs : SList A} -> isProp (P xs))
                   where
  f : (xs : SList A) -> P xs
  f = elimSListSet.f P []* _∷*_ comm* (isProp→isSet isSetSList*)
    where
      abstract
        comm* : (a b : A) {cs : SList A} (cs* : P cs) ->
                PathP (λ i -> P (swap a b cs i)) (a ∷* (b ∷* cs*)) (b ∷* (a ∷* cs*))
        comm* a b {cs} cs* =
          toPathP (isSetSList* (subst P (swap a b cs) (a ∷* (b ∷* cs*))) (b ∷* (a ∷* cs*)))

private
  variable
    ℓ : Level
    A : Type ℓ


_++_ : SList A -> SList A -> SList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
swap a b as i ++ bs = swap a b (as ++ bs) i
isSetSList a b p q i j ++ bs = isSetSList (a ++ bs) (b ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i j

++-unitl : (as : SList A) -> [] ++ as ≡ as
++-unitl as = refl

++-unitr : (as : SList A) -> as ++ [] ≡ as
++-unitr = elimSListProp.f _ refl (λ x p -> cong (x ∷_) p) (isSetSList _ _)

++-assocr : (as bs cs : SList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr = elimSListProp.f _
  (λ _ _ -> refl)
  (λ x p bs cs -> cong (x ∷_) (p bs cs))
  (isPropΠ λ _ -> isPropΠ λ _ -> isSetSList _ _)

++-∷ : (a : A) (as : SList A) -> a ∷ as ≡ as ++ [ a ]
++-∷ a = elimSListProp.f (λ as -> a ∷ as ≡ as ++ [ a ])
  refl
  (λ b {as} p -> swap a b as ∙ cong (b ∷_) p)
  (isSetSList _ _) 

++-comm : (as bs : SList A) -> as ++ bs ≡ bs ++ as
++-comm = elimSListProp.f _
  (sym ∘ ++-unitr)
  (λ a {as} p bs -> cong (a ∷_) (p bs) ∙ cong (_++ as) (++-∷ a bs) ∙ ++-assocr bs [ a ] as)
  (isPropΠ λ _ -> isSetSList _ _)
