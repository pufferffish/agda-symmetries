{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag.FinExcept where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Set.Mon.Array as A
open import Cubical.Structures.Set.Mon.List as L
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Structures.Set.CMon.Bag.Base
open import Cubical.Structures.Set.CMon.Bag.Free
open import Cubical.Relation.Nullary
open import Cubical.Data.Fin.LehmerCode as E

private
  variable
    ℓ : Level
    A : Type ℓ
    n : ℕ

postulate
  TODO : A

abstract
  <-not-dense : ∀ {a b c} -> a < b -> b < suc c -> a < c
  <-not-dense {a} {b} {c} p q with a ≟ c
  ... | lt r = r
  ... | eq r = ⊥.rec (¬n<m<suc-n p (subst (b <_) (congS suc (sym r)) q))
  ... | gt r = ⊥.rec (<-asym (suc-≤-suc r) (≤-trans (≤-suc p) q))

  predℕa<b : ∀ {e a b} -> a < suc b -> e < a -> predℕ a < b
  predℕa<b {e} {a} {b} p (k , q) = subst (_≤ b) (suc-predℕ a lemma) (predℕ-≤-predℕ p)
    where
    lemma : ¬ a ≡ 0
    lemma a≡0 = snotz (sym (+-suc k e) ∙ q ∙ a≡0)

  _<?_on_ : ∀ (a b : ℕ) -> ¬ a ≡ b -> (a < b) ⊎ (b < a)
  a <? b on p with a ≟ b
  ... | lt q = inl q
  ... | gt q = inr q
  ... | eq q = ⊥.rec (p q)

pOut : (k : Fin (suc n)) -> FinExcept k -> Fin n
pOut (k , p) ((j , q) , r) =
  ⊎.rec
    (λ j<k -> j , <-not-dense j<k p)
    (λ k<j -> predℕ j , predℕa<b q k<j)
    (j <? k on (r ∘ Fin-fst-≡ ∘ sym))

pIn : (k : Fin (suc n)) -> Fin n -> FinExcept k
pIn (k , p) (j , q) =
  ⊎.rec
    (λ j<k -> (j , ≤-suc q) , λ r -> <→≢ j<k (sym (congS fst r)))
    (λ k≤j -> fsuc (j , q) , λ r -> ¬m<m (subst (_≤ j) (congS fst r) k≤j))
    (j ≤? k)

_∼ : {k : Fin n} -> (Fin n -> A) -> FinExcept k -> A
f ∼ = f ∘ toFinExc

1+_ : {k : Fin n} -> FinExcept k -> FinExcept (fsuc k)
1+_ = fsucExc

-- postulate
--   punchIn∘Out : (k : Fin (suc n)) → ∀ j → E.punchIn k (E.punchOut k j) ≡ j
-- 
-- -- module _ {k : Fin (suc n)} where
-- --   pIso : Iso (FinExcept k) (Fin n)
-- --   Iso.fun pIso = pOut k
-- --   Iso.inv pIso = pIn k
-- --   Iso.rightInv pIso = punchOut∘In k
-- --   Iso.leftInv pIso = punchIn∘Out k
-- 
-- module _ (n : ℕ) (k : Fin (suc n)) where
--   pIso : Iso (FinExcept k) (Fin n)
--   pIso = equivToIso E.punchOutEquiv
-- 
-- pIn-fsuc-nat : {k : Fin (suc n)} -> 1+_ ∘ pIn k ≡ pIn (fsuc k) ∘ fsuc
-- pIn-fsuc-nat {n = zero} {k = k} = funExt \j -> ⊥.rec (¬Fin0 j)
-- pIn-fsuc-nat {n = suc n} {k = k} = funExt (pIn-fsuc-nat-htpy k)
--   where
--     pIn-fsuc-nat-htpy : (k : Fin (suc (suc n))) (j : Fin (suc n)) -> 1+ (pIn k j) ≡ pIn (fsuc k) (fsuc j)
--     pIn-fsuc-nat-htpy k j =
--       ⊎.rec (\z≡j -> TODO)
--             TODO
--             (fsplit j)
-- 
-- ϕ : Iso (Fin (suc n)) (Unit ⊎ Fin n)
-- ϕ = TODO
-- 
-- H : ∀ {X Y : Type ℓ} -> Iso (Unit ⊎ X) (Unit ⊎ Y) -> Iso X Y
-- H = TODO
-- 
-- module _ {n : ℕ} where
--   G0 : (σ : Iso (Fin (suc n)) (Fin (suc n)))
--     -> Iso (FinExcept {n = suc n} (fzero {k = n})) (FinExcept {n = suc n} (σ .fun fzero))
--   G0 σ = compIso (pIso n fzero)
--                  (compIso (H (compIso (invIso ϕ) (compIso σ ϕ)))
--                           (invIso (pIso n (σ .fun fzero))))
-- 
--   G : Iso (Iso (Fin (suc n)) (Fin (suc n))) (Σ[ k ∈ Fin (suc n) ] Iso (FinExcept {n = suc n} (fzero {k = n})) (FinExcept {n = suc n} k))
--   Iso.fun G σ = σ .fun fzero , G0 σ
--   Iso.inv G = TODO
--   Iso.rightInv G = TODO
--   Iso.leftInv G = TODO
--  