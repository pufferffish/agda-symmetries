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
  swap⁻¹ : (a b : A) (cs : SList A)
       -> swap a b cs ≡ sym (swap b a cs)
  hexagon– : (a b c : A) (cs : SList A)
          -> a ∷ b ∷ c ∷ cs ≡ c ∷ b ∷ a ∷ cs
  hexagon↑ : (a b c : A) (cs : SList A)
           -> Square (\i -> b ∷ swap a c cs i) (hexagon– a b c cs)
                     (swap b a (c ∷ cs)) (swap b c (a ∷ cs))
  hexagon↓ : (a b c : A) (cs : SList A)
           -> Square (hexagon– a b c cs) (swap a c (b ∷ cs))
                     (\i -> a ∷ swap b c cs i) (\i -> c ∷ swap b a cs i)
  isGpdSList : isGroupoid (SList A)

pattern [_] a = a ∷ []

private
  variable
    ℓ : Level
    A : Type ℓ

swap² : (a b : A) (cs : SList A)
     -> swap a b cs ∙ swap b a cs ≡ refl
swap² a b cs = cong (_∙ swap b a cs) (swap⁻¹ a b cs) ∙ lCancel (swap b a cs)

hexagon : (a b c : A) (cs : SList A)
       -> (swap a b (c ∷ cs) ∙ cong (b ∷_) (swap a c cs) ∙ swap b c (a ∷ cs))
        ≡ cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs) ∙ cong (c ∷_) (swap a b cs)
hexagon a b c cs =
  let hex-up = PathP→compPathL (hexagon↑ a b c cs)
      hex-dn = PathP→compPathR (hexagon↓ a b c cs)
  in
    swap a b (c ∷ cs) ∙ cong (b ∷_) (swap a c cs) ∙ swap b c (a ∷ cs)
  ≡⟨ cong (_∙ cong (b ∷_) (swap a c cs) ∙ swap b c (a ∷ cs)) (swap⁻¹ a b (c ∷ cs)) ⟩
    sym (swap b a (c ∷ cs)) ∙ cong (b ∷_) (swap a c cs) ∙ swap b c (a ∷ cs)
  ≡⟨ hex-up ⟩
    hexagon– a b c cs
  ≡⟨ hex-dn ⟩
    cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs) ∙ cong (c ∷_) (sym (swap b a cs))
  ≡⟨ assoc (cong (a ∷_) (swap b c cs)) (swap a c (b ∷ cs)) (cong (c ∷_) (sym (swap b a cs))) ⟩
    (cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs)) ∙ cong (c ∷_) (sym (swap b a cs))
  ≡⟨ cong ((cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs)) ∙_) (cong (cong (c ∷_)) (sym (swap⁻¹ a b cs))) ⟩
    (cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs)) ∙ cong (c ∷_) (swap a b cs)
  ≡⟨ sym (assoc (cong (a ∷_) (swap b c cs)) (swap a c (b ∷ cs)) (cong (c ∷_) (swap a b cs))) ⟩
    cong (a ∷_) (swap b c cs) ∙ swap a c (b ∷ cs) ∙ cong (c ∷_) (swap a b cs)
  ∎

_++_ : SList A -> SList A -> SList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
swap a b as i ++ bs = swap a b (as ++ bs) i
swap⁻¹ a b as i j ++ bs = swap⁻¹ a b (as ++ bs) i j
hexagon– a b c as i ++ bs = hexagon– a b c (as ++ bs) i
hexagon↑ a b c as i j ++ bs = hexagon↑ a b c (as ++ bs) i j
hexagon↓ a b c as i j ++ bs = hexagon↓ a b c (as ++ bs) i j
isGpdSList as cs p q u v i j k ++ bs =
  isGpdSList (as ++ bs) (cs ++ bs) (cong (_++ bs) p) (cong (_++ bs) q)
             (cong (cong (_++ bs)) u) (cong (cong (_++ bs)) v) i j k

++-unitl : (as : SList A) -> [] ++ as ≡ as
++-unitl as = refl

++-unitr : (as : SList A) -> as ++ [] ≡ as
++-unitr [] = refl
++-unitr (a ∷ as) = cong (a ∷_) (++-unitr as)
++-unitr (swap a b as i) j = swap a b (++-unitr as j) i
++-unitr (swap⁻¹ a b as i j) k = swap⁻¹ a b (++-unitr as k) i j
++-unitr (hexagon– a b c as i) j = hexagon– a b c (++-unitr as j) i
++-unitr (hexagon↑ a b c as i j) k = hexagon↑ a b c (++-unitr as k) i j
++-unitr (hexagon↓ a b c as i j) k = hexagon↓ a b c (++-unitr as k) i j
++-unitr (isGpdSList as cs p q u v i j k) l =
  isGpdSList (++-unitr as l) (++-unitr cs l) (cong (\z -> ++-unitr z l) p) (cong (\z -> ++-unitr z l) q)
             (cong (cong (\z -> ++-unitr z l)) u) (cong (cong (\z -> ++-unitr z l)) v) i j k

++-assocr : (as bs cs : SList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr [] bs cs = refl
++-assocr (a ∷ as) bs cs = cong (a ∷_) (++-assocr as bs cs)
++-assocr (swap a b as i) bs cs j = swap a b (++-assocr as bs cs j) i
++-assocr (swap⁻¹ a b as i j) bs cs k = swap⁻¹ a b (++-assocr as bs cs k) i j
++-assocr (hexagon– a b c as i) bs cs j = hexagon– a b c (++-assocr as bs cs j) i
++-assocr (hexagon↑ a b c as i j) bs cs k = hexagon↑ a b c (++-assocr as bs cs k) i j
++-assocr (hexagon↓ a b c as i j) bs cs k = hexagon↓ a b c (++-assocr as bs cs k) i j
++-assocr (isGpdSList as ds p q u v i j k) bs cs l =
  isGpdSList (++-assocr as bs cs l) (++-assocr ds bs cs l) (cong (\z -> ++-assocr z bs cs l) p) (cong (\z -> ++-assocr z bs cs l) q)
             (cong (cong (\z -> ++-assocr z bs cs l)) u) (cong (cong (\z -> ++-assocr z bs cs l)) v) i j k

-- TODO: Define commutativity for SList directly or after truncation
-- To do this directly will probably need coherence for swap
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

-- TODO: Prove SList is free symmetric monoidal on groupoids
--
