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
open import Cubical.Structures.Set.CMon.CList
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
  open BagDef.Free

  module 𝔄 = M.MonSEq < Array A , array-α > array-sat
  module 𝔅 = M.CMonSEq < Bag A , bagFreeDef .α > (bagFreeDef .sat)
  module ℭ = M.CMonSEq < CList A , clist-α > clist-sat

  abstract -- needed so Agda wouldn't get stuck
    fromCListHom : structHom < CList A , clist-α > < Bag A , bagFreeDef .α >
    fromCListHom = ext clistDef squash/ (bagFreeDef .sat) (BagDef.Free.η bagFreeDef)

    fromCList : CList A -> Bag A
    fromCList = fromCListHom .fst

    fromCListIsHom : structIsHom < CList A , clist-α > < Bag A , bagFreeDef .α > fromCList
    fromCListIsHom = fromCListHom .snd

    fromCList-e : fromCList [] ≡ 𝔅.e
    fromCList-e = refl

    fromCList-++ : ∀ xs ys -> fromCList (xs ℭ.⊕ ys) ≡ fromCList xs 𝔅.⊕ fromCList ys
    fromCList-++ xs ys =
      fromCList (xs ℭ.⊕ ys) ≡⟨ sym (fromCListIsHom M.`⊕ ⟪ xs ⨾ ys ⟫) ⟩
      _ ≡⟨ 𝔅.⊕-eta ⟪ xs ⨾ ys ⟫ fromCList ⟩
      _ ∎

    fromCList-η : ∀ x -> fromCList (CL.[ x ]) ≡ Q.[ A.η x ]
    fromCList-η x = congS (λ f -> f x)
      (ext-η clistDef squash/ (bagFreeDef .sat) (BagDef.Free.η bagFreeDef))

  ListToCListHom : structHom < List A , list-α > < CList A , clist-α >
  ListToCListHom = ListDef.Free.ext listDef isSetCList (M.cmonSatMon clist-sat) CL.[_]

  ListToCList : List A -> CList A
  ListToCList = ListToCListHom .fst

  ArrayToCListHom : structHom < Array A , array-α > < CList A , clist-α >
  ArrayToCListHom = structHom∘ < Array A , array-α > < List A , list-α > < CList A , clist-α >
    ListToCListHom ((arrayIsoToList .fun) , arrayIsoToListHom)

  ArrayToCList : Array A -> CList A
  ArrayToCList = ArrayToCListHom .fst

  tab : ∀ n -> (Fin n -> A) -> CList A
  tab = curry ArrayToCList

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
      (λ 0≡σ0 ->
        let IH = toCList-eq (suc n) (f ∘ fsuc) (g ∘ fsuc) (punchOutZero σ (sym 0≡σ0)) (fsuc∘punchOutZero≡ f g σ p (sym 0≡σ0))
        in case1 IH (sym 0≡σ0)
      )
      (λ (k , Sk≡σ0) ->
        case2 k (sym Sk≡σ0)
          (toCList-eq (suc n) (f ∘ fsuc) ((g ∼) ∘ pIn (fsuc k)) (punch-σ σ) (sym (IH1-lemma k Sk≡σ0)))
          (toCList-eq (suc n) (g-σ k) (g ∘ fsuc) (fill-σ k) (sym (funExt (IH2-lemma k Sk≡σ0))))
      )
      (fsplit (σ .fun fzero))
    where
      g-σ : ∀ k -> Fin (suc n) -> A
      g-σ k (zero , p) = g (σ .fun fzero)
      g-σ k (suc j , p) = (g ∼) (1+ (pIn k (j , predℕ-≤-predℕ p)))

      IH1-lemma : ∀ k -> fsuc k ≡ σ .fun fzero -> (g ∼) ∘ pIn (fsuc k) ∘ punch-σ σ .fun ≡ f ∘ fsuc
      IH1-lemma k Sk≡σ0 =
          (g ∼) ∘ pIn (fsuc k) ∘ punch-σ σ .fun
        ≡⟨ congS (λ z -> (g ∼) ∘ pIn z ∘ punch-σ σ .fun) Sk≡σ0 ⟩
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
      IH2-lemma k Sk≡σ0 (zero , r) = congS g Sk≡σ0
      IH2-lemma k Sk≡σ0 (suc j , r) =
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
      case1 IH σ0≡0 =
        tab (suc (suc n)) f ≡⟨⟩
        f fzero ∷ tab (suc n) (f ∘ fsuc) ≡⟨ congS (_∷ tab (suc n) (f ∘ fsuc)) (funExt⁻ p fzero) ⟩
        g (σ .fun fzero) ∷ tab (suc n) (f ∘ fsuc) ≡⟨ congS (\k -> g k ∷ tab (suc n) (f ∘ fsuc)) σ0≡0 ⟩
        g fzero ∷ tab (suc n) (f ∘ fsuc) ≡⟨ congS (g fzero ∷_) IH ⟩
        g fzero ∷ tab (suc n) (g ∘ fsuc) ≡⟨⟩
        tab (suc (suc n)) g ∎
      case2 : (k : Fin (suc n))
            -> σ .fun fzero ≡ fsuc k
            -> tab (suc n) (f ∘ fsuc) ≡ tab (suc n) ((g ∼) ∘ pIn (fsuc k))
            -> tab (suc n) (g-σ k) ≡ tab (suc n) (g ∘ fsuc)
            -> tab (suc (suc n)) f ≡ tab (suc (suc n)) g
      case2 k σ0≡Sk IH1 IH2 =
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

  abstract
    toCList-eq' : ∀ n m f g -> (r : (n , f) ≈ (m , g)) -> tab n f ≡ tab m g
    toCList-eq' n m f g (σ , p) =
      tab n f ≡⟨ toCList-eq n f (g ∘ (finSubst n≡m)) (compIso σ (Fin≅ (sym n≡m))) (sym lemma-α) ⟩
      (uncurry tab) (n , g ∘ finSubst n≡m) ≡⟨ congS (uncurry tab) (Array≡ n≡m λ _ _ -> congS g (Fin-fst-≡ refl)) ⟩
      (uncurry tab) (m , g) ∎
      where
      n≡m : n ≡ m
      n≡m = ≈-length σ
      lemma-α : g ∘ finSubst n≡m ∘ (Fin≅ (sym n≡m)) .fun ∘ σ .fun ≡ f
      lemma-α =
          g ∘ finSubst n≡m ∘ finSubst (sym n≡m) ∘ σ .fun
        ≡⟨ congS {x = finSubst n≡m ∘ finSubst (sym n≡m)} {y = idfun _} (λ h -> g ∘ h ∘ σ .fun) (funExt (λ x -> Fin-fst-≡ refl)) ⟩
          g ∘ σ .fun
        ≡⟨ sym p ⟩
          f ∎

  abstract
    toCList : Bag A -> CList A
    toCList Q.[ (n , f) ] = tab n f
    toCList (eq/ (n , f) (m , g) r i) = toCList-eq' n m f g r i
    toCList (squash/ xs ys p q i j) =
      isSetCList (toCList xs) (toCList ys) (congS toCList p) (congS toCList q) i j

    toCList-η : (xs : Array A) -> toCList Q.[ xs ] ≡ ArrayToCList xs
    toCList-η xs = refl

    toCList-e : toCList 𝔅.e ≡ CL.[]
    toCList-e = refl

    toCList-++ : ∀ xs ys -> toCList (xs 𝔅.⊕ ys) ≡ toCList xs ℭ.⊕ toCList ys
    toCList-++ =
      elimProp (λ _ -> isPropΠ (λ _ -> isSetCList _ _)) λ xs ->
        elimProp (λ _ -> isSetCList _ _) λ ys ->
          sym (ArrayToCListHom .snd M.`⊕ ⟪ xs ⨾ ys ⟫)

    toCList∘fromCList-η : ∀ x -> toCList (fromCList CL.[ x ]) ≡ CL.[ x ]
    toCList∘fromCList-η x = refl

    fromCList∘toCList-η : ∀ x -> fromCList (toCList Q.[ A.η x ]) ≡ Q.[ A.η x ]
    fromCList∘toCList-η x = fromCList-η x

  toCList-fromCList : ∀ xs -> toCList (fromCList xs) ≡ xs
  toCList-fromCList =
    elimCListProp.f _
      (congS toCList fromCList-e ∙ toCList-e) 
      (λ x {xs} p ->
        toCList (fromCList (x ∷ xs)) ≡⟨ congS toCList (fromCList-++ CL.[ x ] xs) ⟩
        toCList (fromCList CL.[ x ] 𝔅.⊕ fromCList xs) ≡⟨ toCList-++ (fromCList CL.[ x ]) (fromCList xs) ⟩
        toCList (fromCList CL.[ x ]) ℭ.⊕ toCList (fromCList xs) ≡⟨ congS (toCList (fromCList CL.[ x ]) ℭ.⊕_) p ⟩
        toCList (fromCList CL.[ x ]) ℭ.⊕ xs ≡⟨ congS {x = toCList (fromCList CL.[ x ])} {y = CL.[ x ]} (ℭ._⊕ xs) (toCList∘fromCList-η x) ⟩
        CL.[ x ] ℭ.⊕ xs
      ∎)
      (isSetCList _ _)

  fromList-toCList : ∀ xs -> fromCList (toCList xs) ≡ xs
  fromList-toCList = elimProp (λ _ -> squash/ _ _) (uncurry lemma)
    where
    lemma : (n : ℕ) (f : Fin n -> A) -> fromCList (toCList Q.[ n , f ]) ≡ Q.[ n , f ]
    lemma zero f =
      fromCList (toCList Q.[ zero , f ]) ≡⟨ congS fromCList (toCList-η (zero , f)) ⟩
      fromCList [] ≡⟨ fromCList-e ⟩
      𝔅.e ≡⟨ congS Q.[_] (e-eta _ (zero , f) refl refl) ⟩
      Q.[ zero , f ] ∎
    lemma (suc n) f =
        fromCList (toCList Q.[ suc n , f ])
      ≡⟨ congS fromCList (toCList-η (suc n , f)) ⟩
        fromCList (ArrayToCList (suc n , f))
      ≡⟨ congS (fromCList ∘ ArrayToCList) (sym (η+fsuc f)) ⟩
        fromCList (ArrayToCList (A.η (f fzero) ⊕ (n , f ∘ fsuc)))
      ≡⟨ congS fromCList $ sym (ArrayToCListHom .snd M.`⊕ ⟪ A.η (f fzero) ⨾ (n , f ∘ fsuc) ⟫) ⟩
        fromCList (f fzero ∷ ArrayToCList (n , f ∘ fsuc))
      ≡⟨ fromCList-++ CL.[ f fzero ] (ArrayToCList (n , f ∘ fsuc)) ⟩
        fromCList CL.[ f fzero ] 𝔅.⊕ fromCList (ArrayToCList (n , f ∘ fsuc))
      ≡⟨ congS (𝔅._⊕ fromCList (ArrayToCList (n , f ∘ fsuc))) (fromCList-η (f fzero)) ⟩
        Q.[ A.η (f fzero) ] 𝔅.⊕ fromCList (ArrayToCList (n , f ∘ fsuc))
      ≡⟨ congS (λ zs -> Q.[ A.η (f fzero) ] 𝔅.⊕ fromCList zs) (sym (toCList-η (n , f ∘ fsuc))) ⟩
        Q.[ A.η (f fzero) ] 𝔅.⊕ fromCList (toCList Q.[ n , f ∘ fsuc ])
      ≡⟨ congS (Q.[ A.η (f fzero) ] 𝔅.⊕_) (lemma n (f ∘ fsuc)) ⟩
        Q.[ A.η (f fzero) ] 𝔅.⊕ Q.[ n , f ∘ fsuc ]
      ≡⟨ QFreeMon.[ A ]-isMonHom (PermRel A) .snd M.`⊕ ⟪ _ ⨾ _ ⟫ ⟩
        Q.[ A.η (f fzero) 𝔄.⊕ (n , f ∘ fsuc) ]
      ≡⟨ congS Q.[_] (η+fsuc f) ⟩
        Q.[ suc n , f ] ∎

  BagToCList : Iso (Bag A) (CList A)
  BagToCList = iso toCList fromCList toCList-fromCList fromList-toCList

bagDef' : ∀ {ℓ ℓ'} -> BagDef.Free ℓ ℓ' 2
bagDef' {ℓ = ℓ} {ℓ' = ℓ'} = BagDef.isoAux .fun (Bag , bagFreeAux)
  where
  clistFreeAux : BagDef.FreeAux ℓ ℓ' 2 CList
  clistFreeAux = (inv BagDef.isoAux clistDef) .snd

  bagFreeAux : BagDef.FreeAux ℓ ℓ' 2 Bag
  bagFreeAux = subst (BagDef.FreeAux ℓ ℓ' 2)
    (funExt λ X -> isoToPath $ invIso (IsoToCList.BagToCList X)) clistFreeAux
