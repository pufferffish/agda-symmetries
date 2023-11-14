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

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    n : ℕ

fsuc≡punchIn : (k : Fin n) -> fsuc k ≡ fst (punchIn fzero k)
fsuc≡punchIn k = refl

except : (t : Fin (suc n)) -> Fin n -> Fin (suc n)
except t k = fst (punchIn t k)

fsuc∘punchOutZero≡ : ∀ {n}
          -> (f g : Fin (suc (suc n)) -> A)
          -> (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) (p : f ≡ g ∘ σ .fun)
          -> (q : σ .fun fzero ≡ fzero)
          -> f ∘ fsuc ≡ g ∘ fsuc ∘ punchOutZero σ q .fun
fsuc∘punchOutZero≡ f g σ p q =
  f ∘ fsuc ≡⟨ congS (_∘ fsuc) p ⟩
  g ∘ σ .fun ∘ fsuc ≡⟨ congS (g ∘_) (funExt (punchOutZero≡fsuc σ q)) ⟩
  g ∘ fsuc ∘ punchOutZero σ q .fun ∎

finNotZIsS : ∀ {n} -> (k : Fin (suc n)) -> ¬ k ≡ fzero -> Σ[ w ∈ Fin n ] (k ≡ fsuc w)
finNotZIsS (zero , p) q = ⊥.rec (q (Fin-fst-≡ refl))
finNotZIsS (suc k , p) q = (k , pred-≤-pred p) , Fin-fst-≡ refl

finZOrS : ∀ {n} -> (k : Fin (suc n)) -> (k ≡ fzero) ⊎ (Σ[ w ∈ Fin n ] (k ≡ fsuc w))
finZOrS k = decRec inl (inr ∘ finNotZIsS k) (discreteFin k fzero)

exceptSuc≡ : (k : Fin (suc n)) -> (x : Fin n) -> except (fsuc k) (fsuc x) ≡ fsuc (except k x)
exceptSuc≡ k x =
  fst (punchIn (fsuc k) (fsuc x)) ≡⟨⟩
  {!   !}

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
        let IH = toCList-eq (suc n) (f ∘ fsuc) (g ∘ fsuc) (punchOutZero σ q) (fsuc∘punchOutZero≡ f g σ p q)
        in case1 IH q
      )
      (λ (k , q) ->
        let
          IH1 = toCList-eq (suc n) (f ∘ fsuc) (g ∘ except (σ .fun fzero)) {!   !} {!   !}
        in case2 k q IH1
      )
      (finZOrS (σ .fun fzero))
    where
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
      case2 : (w : Fin (suc n))
            -> σ .fun fzero ≡ fsuc w
            -> tab (suc n) (f ∘ fsuc) ≡ tab (suc n) (g ∘ except (σ .fun fzero))
            -> tab (suc (suc n)) f ≡ tab (suc (suc n)) g
      case2 k ϕ IH1 =
        comm (f fzero) (g fzero) (tab n (g ∘ fsuc ∘ except k)) eqn1 {!   !}
        where
        eqn1 : tab (suc n) (f ∘ fsuc) ≡ g fzero ∷ tab n (g ∘ fsuc ∘ except k)
        eqn1 =
          tab (suc n) (f ∘ fsuc) ≡⟨ IH1 ⟩
          tab (suc n) (g ∘ except (σ .fun fzero)) ≡⟨⟩
          g (except (σ .fun fzero) fzero) ∷ tab n (g ∘ except (σ .fun fzero) ∘ fsuc) ≡⟨ congS (λ r -> g (except r fzero) ∷ tab n (g ∘ except r ∘ fsuc)) ϕ ⟩
          g (except (fsuc k) fzero) ∷ tab n (g ∘ except (fsuc k) ∘ fsuc) ≡⟨⟩
          g fzero ∷ tab n (g ∘ except (fsuc k) ∘ fsuc) ≡⟨ congS (λ h -> g fzero ∷ tab n (g ∘ h)) (funExt (exceptSuc≡ k)) ⟩
          g fzero ∷ tab n (g ∘ fsuc ∘ except k) ∎

  -- toCList : Bag A -> CList A
  -- toCList Q.[ (n , f) ] = tab n f
  -- toCList (eq/ (n , f) (m , g) r i) = {!!}
  -- toCList (squash/ xs ys p q i j) =
  --   isSetCList (toCList xs) (toCList ys) (congS toCList p) (congS toCList q) i j

  -- toCList-fromCList : ∀ xs -> toCList (fromCList xs) ≡ xs
  -- toCList-fromCList x = {!`  !}
 