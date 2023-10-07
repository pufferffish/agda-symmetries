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

pattern [_] a = a ∷ []

private
  variable
    ℓ : Level
    A : Type ℓ

_++_ : SList A -> SList A -> SList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
swap a b cs i ++ bs = swap a b (cs ++ bs) i

++-unitl : (as : SList A) -> [] ++ as ≡ as
++-unitl as = refl

++-unitr : (as : SList A) -> as ++ [] ≡ as
++-unitr [] = refl
++-unitr (a ∷ as) = cong (a ∷_) (++-unitr as)
++-unitr (swap a b cs i) j = swap a b (++-unitr cs j) i

++-assocr : (as bs cs : SList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr [] bs cs = refl
++-assocr (a ∷ as) bs cs = cong (a ∷_) (++-assocr as bs cs)
++-assocr (swap a b as i) bs cs j = swap a b (++-assocr as bs cs j) i

-- TODO: Define commutativity for SList directly or after truncation
-- To do this directly will probably need coherence for swap
++-∷ : (a : A) (as : SList A) -> a ∷ as ≡ as ++ [ a ]
++-∷ a [] = refl
++-∷ a (b ∷ as) = swap a b as ∙ cong (b ∷_) (++-∷ a as)
++-∷ a (swap b c as i) j =
  {!!}

++-comm : (as bs : SList A) -> as ++ bs ≡ bs ++ as
++-comm [] bs = sym (++-unitr bs)
++-comm (a ∷ as) bs = cong (a ∷_) (++-comm as bs)
                    ∙ cong (_++ as) (++-∷ a bs)
                    ∙ ++-assocr bs [ a ] as
++-comm (swap a b as i) bs = {!!}
