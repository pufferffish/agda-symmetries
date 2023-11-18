{-# OPTIONS --cubical --exact-split #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag.ToCList where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
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
open import Cubical.Data.Fin.LehmerCode hiding (LehmerCode; _∷_; [])

open import Cubical.Structures.Set.CMon.Bag.FinExcept

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    n : ℕ

-- Proof taken from https://arxiv.org/pdf/2110.05412.pdf
module IsoToCList {ℓ} (A : Type ℓ) where
  open import Cubical.Structures.Set.CMon.CList as CL
  open import Cubical.HITs.SetQuotients as Q

  module 𝔅 = M.CMonSEq < Bag A , BagDef.Free.α bagFreeDef > (BagDef.Free.sat bagFreeDef)
  module ℭ = M.CMonSEq < CList A , clist-α > clist-sat

  fromCList : CList A -> Bag A
  fromCList = CL.Free._♯ squash/ (BagDef.Free.sat bagFreeDef) (BagDef.Free.η bagFreeDef)

  ListToCList : List A -> CList A
  ListToCList = (_∷ []) ♯
    where _♯ = (L.Free._♯ isSetCList) (M.cmonSatMon CL.clist-sat)

  tab : ∀ n -> (Fin n -> A) -> CList A
  tab = curry (ListToCList ∘ arrayIsoToList .fun)

  isContr≅ : ∀ {ℓ} {A : Type ℓ} -> isContr A -> isContr (Iso A A)
  isContr≅ ϕ = inhProp→isContr idIso \σ1 σ2 ->
    SetsIso≡ (isContr→isOfHLevel 2 ϕ) (isContr→isOfHLevel 2 ϕ)
             (funExt \x -> isContr→isProp ϕ (σ1 .fun x) (σ2 .fun x))
             (funExt \x -> isContr→isProp ϕ (σ1 .inv x) (σ2 .inv x))

  isContrFin1≅ : isContr (Iso (Fin 1) (Fin 1))
  isContrFin1≅ = isContr≅ isContrFin1

  fsuc∘punchOutZero≡ : ∀ {n}
          -> (f g : Fin (suc (suc n)) -> A)
          -> (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) (p : f ≡ g ∘ σ .fun)
          -> (q : σ .fun fzero ≡ fzero)
          -> f ∘ fsuc ≡ g ∘ fsuc ∘ punchOutZero σ q .fun
  fsuc∘punchOutZero≡ f g σ p q =
    f ∘ fsuc ≡⟨ congS (_∘ fsuc) p ⟩
    g ∘ σ .fun ∘ fsuc ≡⟨ congS (g ∘_) (funExt (punchOutZero≡fsuc σ q)) ⟩
    g ∘ fsuc ∘ punchOutZero σ q .fun ∎

  toCList-eq : ∀ n
             -> (f : Fin n -> A) (g : Fin n -> A) (σ : Iso (Fin n) (Fin n)) (p : f ≡ g ∘ σ .fun)
             -> tab n f ≡ tab n g
  toCList-eq zero f g σ p =
    refl
  toCList-eq (suc zero) f g σ p =
    let q : σ ≡ idIso
        q = isContr→isProp isContrFin1≅ σ idIso
    in congS (tab 1) (p ∙ congS (g ∘_) (congS Iso.fun q))
  toCList-eq (suc (suc n)) f g σ p =
    ⊎.rec
      (λ q ->
        let IH = toCList-eq (suc n) (f ∘ fsuc) (g ∘ fsuc) (punchOutZero σ (sym q)) (fsuc∘punchOutZero≡ f g σ p (sym q))
        in case1 IH (sym q)
      )
      (λ (k , q) ->
        case2 k (sym q)
          (toCList-eq (suc n) (f ∘ fsuc) ((g ∼) ∘ pIn (fsuc k)) (punch-σ σ) (sym (IH1-lemma k q)))
          (toCList-eq (suc n) (g-σ k) (g ∘ fsuc) (fill-σ k) (sym (funExt (IH2-lemma k q))))
      )
      (fsplit (σ .fun fzero))
    where
      g-σ : ∀ k -> Fin (suc n) -> A
      g-σ k (zero , p) = g (σ .fun fzero)
      g-σ k (suc j , p) = (g ∼) (1+ (pIn k (j , predℕ-≤-predℕ p)))

      IH1-lemma : ∀ k -> fsuc k ≡ σ .fun fzero -> (g ∼) ∘ pIn (fsuc k) ∘ punch-σ σ .fun ≡ f ∘ fsuc
      IH1-lemma k q =
          (g ∼) ∘ pIn (fsuc k) ∘ punch-σ σ .fun
        ≡⟨ congS (λ z -> (g ∼) ∘ pIn z ∘ punch-σ σ .fun) q ⟩
          (g ∼) ∘ pIn (σ .fun fzero) ∘ punch-σ σ .fun
        ≡⟨⟩
          (g ∼) ∘ pIn (σ .fun fzero) ∘ pOut (σ .fun fzero) ∘ ((G .fun σ) .snd) .fun ∘ pIn fzero
        ≡⟨ congS (λ h -> (g ∼) ∘ h ∘ ((G .fun σ) .snd) .fun ∘ (invIso pIso) .fun) (funExt (pIn∘Out (σ .fun fzero))) ⟩
          (g ∼) ∘ equivIn σ .fun ∘ pIn fzero
        ≡⟨⟩
          g ∘ σ .fun ∘ fst ∘ pIn fzero
        ≡⟨ congS (_∘ fst ∘ pIn fzero) (sym p) ⟩
          f ∘ fst ∘ pIn fzero
        ≡⟨ congS (f ∘_) (funExt pInZ≡fsuc) ⟩
          f ∘ fsuc ∎

      IH2-lemma : ∀ k -> fsuc k ≡ σ .fun fzero -> (j : Fin (suc n)) -> g (fsuc (fill-σ k .fun j)) ≡ (g-σ k) j
      IH2-lemma k q (zero , r) = congS g q
      IH2-lemma k q (suc j , r) =
          g (fsuc (equivOut {k = k} (compIso pIso (invIso pIso)) .fun (suc j , r)))
        ≡⟨⟩
          g (fsuc (equivOut {k = k} (compIso pIso (invIso pIso)) .fun (j' .fst)))
        ≡⟨ congS (g ∘ fsuc) (equivOut-beta-α {σ = compIso pIso (invIso pIso)} j') ⟩
          g (fsuc (fst (pIn k (pOut fzero j'))))
        ≡⟨⟩
          g (fsuc (fst (pIn k (⊎.rec _ (λ k<j -> predℕ (suc j) , _) (suc j <? 0 on _)))))
        ≡⟨ congS (g ∘ fsuc ∘ fst ∘ pIn k ∘ ⊎.rec _ _) (<?-beta-inr (suc j) 0 _ (suc-≤-suc zero-≤)) ⟩
          (g ∘ fsuc ∘ fst ∘ pIn k) (predℕ (suc j) , _)
        ≡⟨ congS {x = predℕ (suc j) , _} {y = j , predℕ-≤-predℕ r} (g ∘ fsuc ∘ fst ∘ pIn k) (Fin-fst-≡ refl) ⟩
          (g ∘ fsuc ∘ fst ∘ pIn k) (j , predℕ-≤-predℕ r) ∎
        where
        j' : FinExcept fzero
        j' = (suc j , r) , znots ∘ (congS fst)

      case1 : (tab (suc n) (f ∘ fsuc) ≡ tab (suc n) (g ∘ fsuc))
            -> σ .fun fzero ≡ fzero
            -> tab (suc (suc n)) f ≡ tab (suc (suc n)) g
      case1 IH ϕ =
        tab (suc (suc n)) f ≡⟨⟩
        f fzero ∷ tab (suc n) (f ∘ fsuc) ≡⟨ congS (_∷ tab (suc n) (f ∘ fsuc)) (funExt⁻ p fzero) ⟩
        g (σ .fun fzero) ∷ tab (suc n) (f ∘ fsuc) ≡⟨ congS (\k -> g k ∷ tab (suc n) (f ∘ fsuc)) ϕ ⟩
        g fzero ∷ tab (suc n) (f ∘ fsuc) ≡⟨ congS (g fzero ∷_) IH ⟩
        g fzero ∷ tab (suc n) (g ∘ fsuc) ≡⟨⟩
        tab (suc (suc n)) g ∎
      case2 : (k : Fin (suc n))
            -> σ .fun fzero ≡ fsuc k
            -> tab (suc n) (f ∘ fsuc) ≡ tab (suc n) ((g ∼) ∘ pIn (fsuc k))
            -> tab (suc n) (g-σ k) ≡ tab (suc n) (g ∘ fsuc)
            -> tab (suc (suc n)) f ≡ tab (suc (suc n)) g
      case2 k ϕ IH1 IH2 =
        comm (f fzero) (g fzero) (tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc))
          (sym (eqn1 IH1)) (sym (eqn2 IH2))
        where
        eqn1 : tab (suc n) (f ∘ fsuc) ≡ tab (suc n) ((g ∼) ∘ pIn (fsuc k))
              -> g fzero ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc) ≡ tab (suc n) (f ∘ fsuc)
        eqn1 IH =
            g fzero ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc)
          ≡⟨ congS (λ z -> g z ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc)) (Fin-fst-≡ refl) ⟩
            ((g ∼) ∘ pIn (fsuc k)) fzero ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc)
          ≡⟨⟩
            tab (suc n) ((g ∼) ∘ pIn (fsuc k))
          ≡⟨ sym IH ⟩
            tab (suc n) (f ∘ fsuc) ∎

        g-σ≡ : tab (suc n) (g-σ k) ≡ g (σ .fun fzero) ∷ tab n ((g ∼) ∘ 1+_ ∘ pIn k)
        g-σ≡ = congS (λ z -> g (σ .fun fzero) ∷ tab n z)
          (funExt λ z -> congS {x = (fst z , pred-≤-pred (snd (fsuc z)))} ((g ∼) ∘ 1+_ ∘ pIn k) (Fin-fst-≡ refl))

        eqn2 : tab (suc n) (g-σ k) ≡ tab (suc n) (g ∘ fsuc)
            -> f fzero ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc) ≡ tab (suc n) (g ∘ fsuc)
        eqn2 IH2 =
            f fzero ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc)
          ≡⟨ congS (λ h -> h fzero ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc)) p ⟩
            g (σ .fun fzero) ∷ tab n ((g ∼) ∘ pIn (fsuc k) ∘ fsuc)
          ≡⟨ congS (λ h -> g (σ .fun fzero) ∷ tab n ((g ∼) ∘ h)) (sym pIn-fsuc-nat) ⟩
            g (σ .fun fzero) ∷ tab n ((g ∼) ∘ 1+_ ∘ pIn k)
          ≡⟨ sym g-σ≡ ⟩
            tab (suc n) (g-σ k)
          ≡⟨ IH2 ⟩
            tab (suc n) (g ∘ fsuc) ∎

  -- toCList : Bag A -> CList A
  -- toCList Q.[ (n , f) ] = tab n f
  -- toCList (eq/ (n , f) (m , g) r i) = {!!}
  -- toCList (squash/ xs ys p q i j) =
  --   isSetCList (toCList xs) (toCList ys) (congS toCList p) (congS toCList q) i j

  -- toCList-fromCList : ∀ xs -> toCList (fromCList xs) ≡ xs
  -- toCList-fromCList x = {!`  !}
