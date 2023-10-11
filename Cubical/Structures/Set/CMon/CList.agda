{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.CList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma

infixr 20 _∷_

data CList {a} (A : Type a) : Type a where
  [] : CList A
  _∷_ : (a : A) -> (as : CList A) -> CList A
  comm : (a b : A)
      -> {as bs : CList A} (cs : CList A)
      -> (p : as ≡ b ∷ cs) (q : bs ≡ a ∷ cs)
      -> a ∷ as ≡ b ∷ bs
  trunc : isSet (CList A)

pattern [_] a = a ∷ []

module elimCListSet {ℓ p : Level} {A : Type ℓ} (P : CList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : CList A} -> P xs -> P (x ∷ xs))
                   (comm* : (a b : A)
                            -> {as bs : CList A} (cs : CList A)
                            -> (as* : P as)
                            -> (bs* : P bs)
                            -> (p : as ≡ b ∷ cs) (q : bs ≡ a ∷ cs)
                            -> PathP (λ i -> P (comm a b cs p q i)) (a ∷* as*) (b ∷* bs*)
                   )
                   (trunc* : {xs : CList A} -> isSet (P xs))
                   where
  f : (xs : CList A) -> P xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm a b {xs} {ys} cs p q i) = comm* a b cs (f xs) (f ys) p q i
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (\xs -> trunc* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module elimCListProp {ℓ p : Level} {A : Type ℓ} (P : CList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : CList A} -> P xs -> P (x ∷ xs))
                   (trunc* : {xs : CList A} -> isProp (P xs))
                   where
  f : (xs : CList A) -> P xs
  f = elimCListSet.f P []* _∷*_ comm* (isProp→isSet trunc*)
    where
      abstract
        comm* : (a b : A) {as bs : CList A} (cs : CList A) (as* : P as)
                (bs* : P bs) (p : as ≡ (b ∷ cs)) (q : bs ≡ (a ∷ cs)) ->
                PathP (λ i -> P (comm a b cs p q i)) (a ∷* as*) (b ∷* bs*)
        comm* a b cs as* bs* p q =
          toPathP (trunc* (subst P (comm a b cs p q) (a ∷* as*)) (b ∷* bs*))

private
  variable
    ℓ : Level
    A : Type ℓ

_++_ : CList A -> CList A -> CList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
comm a b cs p q i ++ bs = comm a b (cs ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i
trunc a b p q i j ++ bs = trunc (a ++ bs) (b ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i j

++-unitl : (as : CList A) -> [] ++ as ≡ as
++-unitl as = refl

++-unitr : (as : CList A) -> as ++ [] ≡ as
++-unitr = elimCListProp.f _ refl (λ a p -> cong (a ∷_) p) (trunc _ _)

++-assocr : (as bs cs : CList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr = elimCListProp.f _
  (λ _ _ -> refl)
  (λ x p bs cs -> cong (x ∷_) (p bs cs))
  (isPropΠ λ _ -> isPropΠ λ _ -> trunc _ _)

swap : (a b : A) (cs : CList A) -> a ∷ b ∷ cs ≡ b ∷ a ∷ cs
swap a b = elimCListProp.f _
  (comm a b [] refl refl)
  (λ x {xs} p -> comm a b (x ∷ xs) refl refl)
  (trunc _ _)

++-∷ : (a : A) (as : CList A) -> a ∷ as ≡ as ++ [ a ]
++-∷ a = elimCListProp.f (λ as -> a ∷ as ≡ as ++ [ a ])
  refl
  (λ b {as} p -> swap a b as ∙ cong (b ∷_) p)
  (trunc _ _) 

++-comm : (as bs : CList A) -> as ++ bs ≡ bs ++ as
++-comm = elimCListProp.f _
  (sym ∘ ++-unitr)
  (λ a {as} p bs -> cong (a ∷_) (p bs) ∙ cong (_++ as) (++-∷ a bs) ∙ ++-assocr bs [ a ] as)
  (isPropΠ λ _ -> trunc _ _)
