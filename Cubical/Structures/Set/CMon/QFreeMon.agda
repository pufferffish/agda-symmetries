{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.QFreeMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q
open import Cubical.Data.List as L

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

record PermRelation : Typeω where
  field
    freeMon : Free 2

    R : ∀ {ℓ ℓ'} {A : Type ℓ} -> freeMon .F A -> freeMon .F A -> Type ℓ'

    perm-append : ∀ {ℓ ℓ'} {A : Type ℓ} (as bs : freeMon .F A)
      -> (p : R {ℓ' = ℓ'} as bs)
      -> (cs : freeMon .F A)
      -> R {ℓ' = ℓ'}
          (freeMon .α (M.`⊕ , lookup (as ∷ cs ∷ [])))
          (freeMon .α (M.`⊕ , lookup (bs ∷ cs ∷ [])))
    perm-prepend : ∀ {ℓ ℓ'} {A : Type ℓ} (bs cs : freeMon .F A) -> (as : freeMon .F A)
      -> (p : R {ℓ' = ℓ'} bs cs)
      -> R {ℓ' = ℓ'}
          (freeMon .α (M.`⊕ , lookup (as ∷ bs ∷ [])))
          (freeMon .α (M.`⊕ , lookup (as ∷ cs ∷ [])))

    ⊕-unitlₚ : ∀ {ℓ ℓ'} {A : Type ℓ}
      -> (as : freeMon .F A)
      -> R {ℓ' = ℓ'}
          (freeMon .α (M.`⊕ , lookup ((freeMon .α (M.`e , lookup [])) ∷ as ∷ [])))
          as
    ⊕-unitrₚ : ∀ {ℓ ℓ'} {A : Type ℓ}
      -> (as : freeMon .F A)
      -> R {ℓ' = ℓ'}
          (freeMon .α (M.`⊕ , lookup (as ∷ (freeMon .α (M.`e , lookup [])) ∷ [])))
          as
    ⊕-assocrₚ : ∀ {ℓ ℓ'} {A : Type ℓ} -> (as bs cs : freeMon .F A)
      -> R {ℓ' = ℓ'}
          (freeMon .α (M.`⊕ , lookup (freeMon .α (M.`⊕ , lookup (as ∷ bs ∷ [])) ∷ cs ∷ [])))
          (freeMon .α (M.`⊕ , lookup (as ∷ freeMon .α (M.`⊕ , lookup (bs ∷ cs ∷ [])) ∷ [])))
    ⊕-commₚ : ∀ {ℓ ℓ'} {A : Type ℓ} -> (as bs : freeMon .F A)
      -> R {ℓ' = ℓ'}
          (freeMon .α (M.`⊕ , (lookup (as ∷ bs ∷ []))))
          (freeMon .α (M.`⊕ , (lookup (bs ∷ as ∷ []))))

    f-≅ₚ : ∀ {ℓ ℓ' ℓB} {A : Type ℓ} {𝔜 : struct ℓB M.MonSig}
      (𝔜-cmon : 𝔜 ⊨ M.CMonSEq)
      (f : structHom < freeMon .F A , freeMon .α > 𝔜)
      (xs zs : freeMon .F A)
      -> R {ℓ' = ℓ'} xs zs -> (f .fst) xs ≡ (f .fst) zs


module QFreeMon {ℓr} (r : PermRelation) where
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
    module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon
  
    𝔛 : M.CMonStruct
    𝔛 = < QFreeMon A , qFreeMon-α >

    module _ (f : A -> 𝔜 .car) where
      f♯ : structHom < r .freeMon .F A , r .freeMon .α > 𝔜
      f♯ = ext (r .freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

      _♯ : QFreeMon A -> 𝔜 .car    
      Q.[ as ] ♯ = f♯ .fst as 
      eq/ as bs p i ♯ = P.rec (isSet𝔜 _ _) (r .f-≅ₚ 𝔜-cmon f♯ as bs) p i
      squash/ xs ys p q i j ♯ = isSet𝔜 (xs ♯) (ys ♯) (cong _♯ p) (cong _♯ q) i j

      ♯-++ : ∀ xs ys -> (xs ⊕/ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
      ♯-++ =
        elimProp (λ _ -> isPropΠ λ _ -> isSet𝔜 _ _) λ xs ->
          elimProp (λ _ -> isSet𝔜 _ _) λ ys ->
            f♯ .fst (xs ⊕ ys) ≡⟨ sym (f♯ .snd M.`⊕ (lookup (xs ∷ ys ∷ []))) ⟩
            _ ≡⟨ 𝔜.⊕-eta (lookup (xs ∷ ys ∷ [])) (f♯ .fst) ⟩
            _ ∎
  
      ♯-isMonHom : structHom 𝔛 𝔜
      fst ♯-isMonHom = _♯
      snd ♯-isMonHom M.`e i = 𝔜.e-eta ∙ f♯ .snd M.`e (lookup [])
      snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ ∙ sym (♯-++ (i fzero) (i fone))

    qFreeMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
    qFreeMonEquiv =
      isoToEquiv (iso (λ g -> g .fst ∘ η/) ♯-isMonHom {!   !} {!   !})

  
  qFreeMon-sat : ∀ {X : Type ℓr} -> < QFreeMon X , qFreeMon-α > ⊨ M.CMonSEq
  qFreeMon-sat (M.`mon M.`unitl) ρ = ⊕-unitl (ρ fzero)
  qFreeMon-sat (M.`mon M.`unitr) ρ = ⊕-unitr (ρ fzero)
  qFreeMon-sat (M.`mon M.`assocr) ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)
  qFreeMon-sat M.`comm ρ = ⊕-comm (ρ fzero) (ρ fone)
 
module QFreeMonDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq
  
qFreeMonDef : PermRelation -> QFreeMonDef.Free 2
F (qFreeMonDef rel) = QFreeMon.QFreeMon rel
η (qFreeMonDef rel) = QFreeMon.η/ rel
α (qFreeMonDef rel) = QFreeMon.qFreeMon-α rel
sat (qFreeMonDef rel) = QFreeMon.qFreeMon-sat rel
isFree (qFreeMonDef rel) isSet𝔜 satMon = (QFreeMon.IsFree.qFreeMonEquiv rel isSet𝔜 satMon) .snd
 