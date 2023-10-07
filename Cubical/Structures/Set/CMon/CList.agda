{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.CList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma

data CList {a} (A : Type a) : Type a where
  [] : CList A
  _∷_ : (a : A) -> (as : CList A) -> CList A
  comm : (a b : A)
      -> {as bs : CList A} (cs : CList A)
      -> (p : as ≡ b ∷ cs) (q : bs ≡ a ∷ cs)
      -> a ∷ as ≡ b ∷ bs

-- TODO: Add truncation to the CList HIT or truncate the CList type
-- TODO: Define eliminators for CList

private
  variable
    ℓ : Level
    A : Type ℓ

_++_ : CList A -> CList A -> CList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
comm a b cs p q i ++ bs = comm a b (cs ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i

++-unitl : (as : CList A) -> [] ++ as ≡ as
++-unitl as = refl

-- TODO: Define unitr for CList directly or after truncation
++-unitr : (as : CList A) -> as ++ [] ≡ as
++-unitr [] = refl
++-unitr (a ∷ as) = cong (a ∷_) (++-unitr as)
++-unitr (comm a b {as} {bs} cs p q i) j =
  comm a b {++-unitr as j} {++-unitr bs j} (++-unitr cs j)
       {!!}
       {!!} i

-- TODO: Define assocr for CList directly or after truncation
++-assocr : (as bs cs : CList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr [] bs cs = refl
++-assocr (a ∷ as) bs cs = cong (a ∷_) (++-assocr as bs cs)
++-assocr (comm a b {xs} {ys} zs p q i) bs cs j =
  comm a b {++-assocr xs bs cs j} {++-assocr ys bs cs j} (++-assocr zs bs cs j)
       {!!} {!!} i

-- TODO: Define commutativity for CList directly or after truncation
-- Doing this directly will need coherence for comm
