{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.QFreeMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q
open import Cubical.Data.List

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)

open F.Definition M.MonSig M.MonEqSig M.MonSEq
open F.Definition.Free

record PermRelation {ℓ : Level} : Typeω where
  field
    freeMon : Free 2

    R : {A : Type ℓ} -> freeMon .F A -> freeMon .F A -> Type ℓ

    perm-append : {A : Type ℓ} (as bs : freeMon .F A)
      -> (p : R as bs)
      -> (cs : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , lookup (as ∷ cs ∷ []))) (freeMon .α (M.`⊕ , lookup (bs ∷ cs ∷ [])))
    perm-prepend : {A : Type ℓ} (bs cs : freeMon .F A) -> (as : freeMon .F A)
      -> (p : R bs cs)
      -> R (freeMon .α (M.`⊕ , lookup (as ∷ bs ∷ []))) (freeMon .α (M.`⊕ , lookup (as ∷ cs ∷ [])))

    ⊕-unitlₚ : {A : Type ℓ}
      -> (as : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , lookup ((freeMon .α (M.`e , lookup [])) ∷ as ∷ []))) as
    ⊕-unitrₚ : {A : Type ℓ}
      -> (as : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , lookup (as ∷ (freeMon .α (M.`e , lookup [])) ∷ []))) as
    ⊕-assocrₚ : {A : Type ℓ} -> (as bs cs : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , lookup (freeMon .α (M.`⊕ , lookup (as ∷ bs ∷ [])) ∷ cs ∷ [])))
           (freeMon .α (M.`⊕ , lookup (as ∷ freeMon .α (M.`⊕ , lookup (bs ∷ cs ∷ [])) ∷ [])))
    ⊕-commₚ : {A : Type ℓ} -> (as bs : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , (lookup (as ∷ bs ∷ []))))
           (freeMon .α (M.`⊕ , (lookup (bs ∷ as ∷ []))))

    f-≅ₚ : ∀ {ℓB} {A : Type ℓ} {𝔜 : struct ℓB M.MonSig}
      (𝔜-cmon : 𝔜 ⊨ M.CMonSEq)
      (f : structHom < freeMon .F A , freeMon .α > 𝔜)
      (xs zs : freeMon .F A)
      -> R xs zs -> (f .fst) xs ≡ (f .fst) zs

module QFreeMon {ℓr} (r : PermRelation {ℓr}) where
  open PermRelation

  private
    variable
      ℓ : Level
      A : Type ℓr
      B : Type ℓ

  _≈ₚ_ : r .freeMon .F A -> r .freeMon .F A -> Type ℓr
  xs ≈ₚ ys = ∥ (r .R) xs ys ∥₁

  QFreeMon : Type ℓr -> Type ℓr
  QFreeMon A = r .freeMon .F A / _≈ₚ_

  e : r .freeMon .F A
  e = r .freeMon .α (M.`e , (lookup []))
  
  _⊕_ : r .freeMon .F A -> r .freeMon .F A -> r .freeMon .F A
  xs ⊕ ys = r .freeMon .α (M.`⊕ , (lookup (xs ∷ ys ∷ [])))

  e/ : QFreeMon A
  e/ = Q.[ e ]
  
  η/ : A -> QFreeMon A
  η/ x = Q.[ r .freeMon .η x ]

  _⊕/_ : QFreeMon A -> QFreeMon A -> QFreeMon A
  _⊕/_ = Q.rec2 squash/
    (λ xs ys -> Q.[ xs ⊕ ys ])
    (λ as bs cs p -> eq/ (as ⊕ cs) (bs ⊕ cs) (P.map (λ p -> r .perm-append as bs p cs) p))
    (λ as bs cs p -> eq/ (as ⊕ bs) (as ⊕ cs) (P.map (λ p -> r .perm-prepend bs cs as p) p))

  ⊕-unitl : (as : QFreeMon A) -> e/ ⊕/ as ≡ as
  ⊕-unitl = elimProp (λ _ -> squash/ _ _) (λ as -> eq/ _ _ ∣  (r .⊕-unitlₚ) as ∣₁)

  ⊕-unitr : (as : QFreeMon A) -> as ⊕/ e/ ≡ as
  ⊕-unitr = elimProp (λ _ -> squash/ _ _) (λ as -> eq/ _ _ ∣ (r .⊕-unitrₚ) as ∣₁)

  ⊕-assocr : (as bs cs : QFreeMon A) -> (as ⊕/ bs) ⊕/ cs ≡ as ⊕/ (bs ⊕/ cs)
  ⊕-assocr =
    elimProp (λ _ -> isPropΠ (λ _ -> isPropΠ (λ _ -> squash/ _ _))) λ xs ->
      elimProp (λ _ -> isPropΠ λ _ -> squash/ _ _) λ ys ->
        elimProp (λ _ -> squash/ _ _) λ zs ->
          eq/ _ _ ∣ (r .⊕-assocrₚ) xs ys zs ∣₁
  
  ⊕-comm : (xs ys : QFreeMon A) -> xs ⊕/ ys ≡ ys ⊕/ xs
  ⊕-comm =
    elimProp (λ _ -> isPropΠ (λ _ -> squash/ _ _)) λ xs ->
      elimProp (λ _ -> squash/ _ _) λ ys ->
        eq/ _ _ ∣ (r .⊕-commₚ) xs ys ∣₁

  qFreeMon-α : {X : Type ℓr} -> sig M.MonSig (QFreeMon X) -> QFreeMon X
  qFreeMon-α (M.`e , i) = Q.[ e ]
  qFreeMon-α (M.`⊕ , i) = i fzero ⊕/ i fone

  module IsFree {y : Level} {A : Type ℓr} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
    module 𝔜' = M.CMonSEq 𝔜 𝔜-cmon
  
    𝔛 : M.CMonStruct
    𝔛 = < QFreeMon A , qFreeMon-α >

    module _ (f : A -> 𝔜 .car) where
      _♯ₚ : QFreeMon A -> 𝔜 .car    
      Q.[ as ] ♯ₚ =
        (ext (r .freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon) f) .fst as 
      eq/ as bs p i ♯ₚ =
        P.rec (isSet𝔜 _ _) (r .f-≅ₚ 𝔜-cmon (ext (r .freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon) f) as bs) p i
      squash/ xs ys p q i j ♯ₚ = isSet𝔜 (xs ♯ₚ) (ys ♯ₚ) (cong _♯ₚ p) (cong _♯ₚ q) i j


