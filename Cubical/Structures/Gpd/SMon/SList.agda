{-# OPTIONS --cubical #-}

module Cubical.Structures.Gpd.SMon.SList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma

infixr 20 _∷_

data SList {a} (A : Type a) : Type a where
  [] : SList A
  _∷_ : (a : A) -> (as : SList A) -> SList A
  swap : (a b : A) (cs : SList A)
      -> a ∷ b ∷ cs ≡ b ∷ a ∷ cs
  swap² : (a b : A) (cs : SList A)
       -> swap a b cs ≡ sym (swap b a cs)
  hexagon– : ∀ a b c cs -> a ∷ b ∷ c ∷ cs ≡ c ∷ b ∷ a ∷ cs
  hexagon↑ : ∀ a b c cs -> Square (\i -> b ∷ swap a c cs i) (hexagon– a b c cs)
                                 (swap b a (c ∷ cs)) (swap b c (a ∷ cs))
  hexagon↓ : ∀ a b c cs -> Square (hexagon– a b c cs) (swap a c (b ∷ cs))
                                 (\i -> a ∷ swap b c cs i) (\i -> c ∷ swap b a cs i)
  isGpdSList : isGroupoid (SList A)

pattern [_] a = a ∷ []

private
  variable
    ℓ : Level
    A : Type ℓ

hexagon : (a b c : A) (cs : SList A)
       -> (swap a b (c ∷ cs) ∙ cong (b ∷_) (swap a c cs) ∙ swap b c (a ∷ cs))
        ≡ cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs) ∙ cong (c ∷_) (swap a b cs)
hexagon a b c cs = {!!}

_++_ : SList A -> SList A -> SList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
swap a b as i ++ bs = swap a b (as ++ bs) i
swap² a b as i j ++ bs = swap² a b (as ++ bs) i j
hexagon– a b c as i ++ bs = hexagon– a b c (as ++ bs) i
hexagon↑ a b c as i j ++ bs = hexagon↑ a b c (as ++ bs) i j
hexagon↓ a b c as i j ++ bs = hexagon↓ a b c (as ++ bs) i j
isGpdSList a b p q x y i j k ++ bs = {!!}

-- [] ++ bs = bs
-- (a ∷ as) ++ bs = a ∷ (as ++ bs)
-- swap a b cs i ++ bs = swap a b (cs ++ bs) i
-- hexagon a b c cs i j ++ bs = hexagon a b c (cs ++ bs) i {!j!}

-- ++-unitl : (as : SList A) -> [] ++ as ≡ as
-- ++-unitl as = refl

-- ++-unitr : (as : SList A) -> as ++ [] ≡ as
-- ++-unitr [] = refl
-- ++-unitr (a ∷ as) = cong (a ∷_) (++-unitr as)
-- ++-unitr (swap a b cs i) j = swap a b (++-unitr cs j) i

-- ++-assocr : (as bs cs : SList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
-- ++-assocr [] bs cs = refl
-- ++-assocr (a ∷ as) bs cs = cong (a ∷_) (++-assocr as bs cs)
-- ++-assocr (swap a b as i) bs cs j = swap a b (++-assocr as bs cs j) i

-- -- TODO: Define commutativity for SList directly or after truncation
-- -- To do this directly will probably need coherence for swap
-- ++-∷ : (a : A) (as : SList A) -> a ∷ as ≡ as ++ [ a ]
-- ++-∷ a [] = refl
-- ++-∷ a (b ∷ as) = swap a b as ∙ cong (b ∷_) (++-∷ a as)
-- ++-∷ a (swap b c as i) =
--   {!!}

-- ++-comm : (as bs : SList A) -> as ++ bs ≡ bs ++ as
-- ++-comm [] bs = sym (++-unitr bs)
-- ++-comm (a ∷ as) bs = cong (a ∷_) (++-comm as bs)
--                     ∙ cong (_++ as) (++-∷ a bs)
--                     ∙ ++-assocr bs [ a ] as
-- ++-comm (swap a b as i) bs = {!!}
