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

  a>b→a≠0 : ∀ {a b} -> a > b -> ¬ a ≡ 0
  a>b→a≠0 {a} {b} (k , p) a≡0 = snotz (sym (+-suc k b) ∙ p ∙ a≡0)

  predℕa<b : ∀ {e a b} -> a < suc b -> e < a -> predℕ a < b
  predℕa<b {e} {a} {b} p q = subst (_≤ b) (suc-predℕ a (a>b→a≠0 q)) (predℕ-≤-predℕ p)

  _<?_on_ : ∀ (a b : ℕ) -> ¬ a ≡ b -> (a < b) ⊎ (b < a)
  a <? b on p with a ≟ b
  ... | lt q = inl q
  ... | gt q = inr q
  ... | eq q = ⊥.rec (p q)
  
  <?-beta-inl : ∀ (a b : ℕ) -> (p : ¬ a ≡ b) -> (q : a < b) -> a <? b on p ≡ inl q
  <?-beta-inl a b p q with a ≟ b
  ... | lt r = congS inl (isProp≤ _ _)
  ... | eq r = ⊥.rec (p r)
  ... | gt r = ⊥.rec (<-asym r (<-weaken q))
  
  <?-beta-inr : ∀ (a b : ℕ) -> (p : ¬ a ≡ b) -> (q : a > b) -> a <? b on p ≡ inr q
  <?-beta-inr a b p q with a ≟ b
  ... | lt r = ⊥.rec (<-asym r (<-weaken q))
  ... | eq r = ⊥.rec (p r)
  ... | gt r = congS inr (isProp≤ _ _)
  
  ≤?-beta-inl : ∀ (a b : ℕ) -> (p : a < b) -> a ≤? b ≡ inl p
  ≤?-beta-inl a b p with a ≤? b
  ... | inl q = congS inl (isProp≤ _ _)
  ... | inr q = ⊥.rec (<-asym p q)
  
  ≤?-beta-inr : ∀ (a b : ℕ) -> (p : b ≤ a) -> a ≤? b ≡ inr p
  ≤?-beta-inr a b p with a ≤? b
  ... | inl q = ⊥.rec (<-asym q p)
  ... | inr q = congS inr (isProp≤ _ _)

  FinExcept≡ : ∀ {n k} -> (a b : FinExcept {n = n} k) -> a .fst .fst ≡ b .fst .fst -> a ≡ b
  FinExcept≡ a b p = Σ≡Prop (λ _ -> isProp¬ _) (Fin-fst-≡ p)

pOut : ∀ {n} -> (k : Fin (suc n)) -> FinExcept k -> Fin n
pOut {n} (k , p) ((j , q) , r) =
  ⊎.rec
    (λ j<k -> j , <-not-dense j<k p)
    (λ k<j -> predℕ j , predℕa<b q k<j)
    (j <? k on j≠k)
  where
    abstract -- DO NOT MOVE THIS OUT OF ABSTRACT OR IT WILL TAKE FOREVER TO TYPE CHECK
      j≠k : ¬ j ≡ k
      j≠k = r ∘ Fin-fst-≡ ∘ sym

pIn : (k : Fin (suc n)) -> Fin n -> FinExcept k
pIn (k , p) (j , q) =
  ⊎.rec
    (λ j<k -> (j , ≤-suc q) , except1 j<k)
    (λ k≤j -> fsuc (j , q) , except2 k≤j)
    (j ≤? k)
  where
    abstract
      except1 : j < k -> ¬ (k , p) ≡ (j , ≤-suc q)
      except1 j<k r = <→≢ j<k (sym (congS fst r))
      except2 : k ≤ j -> ¬ (k , p) ≡ fsuc (j , q)
      except2 k≤j r = ¬m<m (subst (_≤ j) (congS fst r) k≤j)

_∼ : {k : Fin n} -> (Fin n -> A) -> FinExcept k -> A
f ∼ = f ∘ toFinExc

1+_ : {k : Fin n} -> FinExcept k -> FinExcept (fsuc k)
1+_ = fsucExc

pIn∘Out : (k : Fin (suc n)) -> ∀ j -> pIn k (pOut k j) ≡ j
pIn∘Out (k , p) ((j , q) , r) =
  ⊎.rec
    (λ j<k ->
        pIn (k , p) (pOut (k , p) ((j , q) , r))
      ≡⟨⟩
        pIn (k , p) (⊎.rec (λ j<k -> j , _) _ (j <? k on _))
      ≡⟨ congS (pIn (k , p) ∘ ⊎.rec _ _) (<?-beta-inl j k _ j<k) ⟩
        pIn (k , p) (j , <-not-dense j<k p)
      ≡⟨⟩
        ⊎.rec (λ j<k -> (j , _) , _) _ (j ≤? k)
      ≡⟨ congS (⊎.rec (λ j<k -> (j , _) , _) _) (≤?-beta-inl j k j<k) ⟩
        (j , ≤-suc (<-not-dense j<k p)) , _
      ≡⟨ FinExcept≡ _ _ refl ⟩
        ((j , q) , r)
    ∎)
    (λ k<j ->
        pIn (k , p) (pOut (k , p) ((j , q) , r))
      ≡⟨⟩
        pIn (k , p) (⊎.rec _ (λ k<j -> predℕ j , predℕa<b q k<j) (j <? k on _))
      ≡⟨ congS (pIn (k , p) ∘ ⊎.rec _ _) (<?-beta-inr j k _ k<j) ⟩
        pIn (k , p) (predℕ j , predℕa<b q k<j)
      ≡⟨⟩
        ⊎.rec _ (λ k≤predℕj -> fsuc (predℕ j , _) , _) (predℕ j ≤? k)
      ≡⟨ congS (⊎.rec _ _) (≤?-beta-inr (predℕ j) k (predℕ-≤-predℕ k<j)) ⟩
        (fsuc (predℕ j , predℕa<b q k<j) , _)
      ≡⟨ FinExcept≡ _ _ (sym (suc-predℕ j (a>b→a≠0 k<j))) ⟩
        ((j , q) , r) ∎
    )
    (j <? k on (r ∘ Fin-fst-≡ ∘ sym))

pOut∘In : (k : Fin (suc n)) -> ∀ j -> pOut k (pIn k j) ≡ j
pOut∘In (k , p) (j , q) =
  ⊎.rec
    (λ j<k ->
        pOut (k , p) (pIn (k , p) (j , q))
      ≡⟨⟩
        pOut (k , p) (⊎.rec (λ j<k -> (j , ≤-suc q) , _) _ (j ≤? k))
      ≡⟨ congS (pOut (k , p) ∘ ⊎.rec _ _) (≤?-beta-inl j k j<k) ⟩
        pOut (k , p) ((j , ≤-suc q) , _)
      ≡⟨⟩
        ⊎.rec (λ j<k -> j , <-not-dense j<k p) _ (j <? k on _)
      ≡⟨ congS (⊎.rec _ _) (<?-beta-inl j k _ j<k) ⟩
        (j , <-not-dense j<k p)
      ≡⟨ Fin-fst-≡ refl ⟩
         (j , q)
    ∎)
    (λ k≤j ->
        pOut (k , p) (pIn (k , p) (j , q))
      ≡⟨⟩
        pOut (k , p) (⊎.rec _ (λ k≤j -> fsuc (j , q) , _) (j ≤? k))
      ≡⟨ congS (pOut (k , p) ∘ ⊎.rec _ _) (≤?-beta-inr j k k≤j) ⟩
        pOut (k , p) (fsuc (j , q) , _)
      ≡⟨⟩
        ⊎.rec _ (λ k<sucj -> predℕ (suc j) , _) (suc j <? k on _)
      ≡⟨ congS (⊎.rec _ _) (<?-beta-inr (suc j) k _ (suc-≤-suc k≤j)) ⟩
        (j , predℕa<b (snd (fsuc (j , q))) (suc-≤-suc k≤j))
      ≡⟨ Fin-fst-≡ refl ⟩
        (j , q)
    ∎)
    (j ≤? k)

module _ {k : Fin (suc n)} where
  pIso : Iso (FinExcept k) (Fin n)
  Iso.fun pIso = pOut k
  Iso.inv pIso = pIn k
  Iso.rightInv pIso = pOut∘In k
  Iso.leftInv pIso = pIn∘Out k

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