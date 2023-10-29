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
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open F.Definition M.MonSig M.MonEqSig M.MonSEq
open F.Definition.Free

record PermRelation {ℓ ℓ' : Level} (freeMon : Free ℓ ℓ' 2) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    R : {A : Type ℓ} -> freeMon .F A -> freeMon .F A -> Type ℓ

    perm-refl : {A : Type ℓ} -> (as : freeMon .F A) -> R as as

    perm-append : {A : Type ℓ} (as bs : freeMon .F A)
      -> (p : R as bs)
      -> (cs : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , ⟪ as ⨾ cs ⟫)) (freeMon .α (M.`⊕ , ⟪ bs ⨾ cs ⟫))
    perm-prepend : {A : Type ℓ} (bs cs : freeMon .F A) -> (as : freeMon .F A)
      -> (p : R bs cs)
      -> R (freeMon .α (M.`⊕ , ⟪ as ⨾ bs ⟫)) (freeMon .α (M.`⊕ , ⟪ as ⨾ cs ⟫))

    ⊕-commₚ : {A : Type ℓ} -> (as bs : freeMon .F A)
      -> R (freeMon .α (M.`⊕ , ⟪ as ⨾ bs ⟫)) (freeMon .α (M.`⊕ , ⟪ bs ⨾ as ⟫))

    f-≅ₚ : {A : Type ℓ} {𝔜 : struct ℓ' M.MonSig}
      (𝔜-cmon : 𝔜 ⊨ M.CMonSEq)
      (f : structHom < freeMon .F A , freeMon .α > 𝔜)
      (xs zs : freeMon .F A)
      -> R xs zs -> (f .fst) xs ≡ (f .fst) zs

module QFreeMon {ℓr ℓB} {freeMon : Free ℓr ℓB 2} (r : PermRelation freeMon) where
  open PermRelation

  _≈ₚ_ : ∀ {A : Type ℓr} -> freeMon .F A -> freeMon .F A -> Type ℓr
  xs ≈ₚ ys = ∥ (r .R) xs ys ∥₁

  QFreeMon : Type ℓr -> Type ℓr
  QFreeMon A = freeMon .F A / _≈ₚ_

  module _ {A : Type ℓr} where
    𝔉 : M.MonStruct
    𝔉 = < freeMon .F A , freeMon .α >
 
    module 𝔉 = M.MonSEq 𝔉 (freeMon .sat)

    e : freeMon .F A
    e = 𝔉.e
  
    _⊕_ : freeMon .F A -> freeMon .F A -> freeMon .F A
    _⊕_ = 𝔉._⊕_
 
    e/ : QFreeMon A
    e/ = Q.[ e ]
  
    η/ : A -> QFreeMon A
    η/ x = Q.[ freeMon .η x ]
 
    _⊕/_ : QFreeMon A -> QFreeMon A -> QFreeMon A
    _⊕/_ = Q.rec2 squash/
      (λ xs ys -> Q.[ xs ⊕ ys ])
      (λ as bs cs p -> eq/ (as ⊕ cs) (bs ⊕ cs) (P.map (λ p -> r .perm-append as bs p cs) p))
      (λ as bs cs p -> eq/ (as ⊕ bs) (as ⊕ cs) (P.map (λ p -> r .perm-prepend bs cs as p) p))
 
    ⊕-unitl : (as : QFreeMon A) -> e/ ⊕/ as ≡ as
    ⊕-unitl = elimProp
      (λ _ -> squash/ _ _)
      (λ as -> eq/ _ _ ∣ subst (λ z -> r .R z as) (sym (𝔉.unitl as)) (r .perm-refl as) ∣₁)
 
    ⊕-unitr : (as : QFreeMon A) -> as ⊕/ e/ ≡ as
    ⊕-unitr = elimProp
      (λ _ -> squash/ _ _)
      (λ as -> eq/ _ _ ∣ subst (λ z -> r .R z as) (sym (𝔉.unitr as)) (r .perm-refl as) ∣₁)
 
    ⊕-assocr : (as bs cs : QFreeMon A) -> (as ⊕/ bs) ⊕/ cs ≡ as ⊕/ (bs ⊕/ cs)
    ⊕-assocr =
      elimProp (λ _ -> isPropΠ (λ _ -> isPropΠ (λ _ -> squash/ _ _))) λ xs ->
        elimProp (λ _ -> isPropΠ λ _ -> squash/ _ _) λ ys ->
          elimProp (λ _ -> squash/ _ _) λ zs ->
            eq/ _ _ ∣ subst (r .R ((xs ⊕ ys) ⊕ zs)) (𝔉.assocr xs ys zs) (r .perm-refl ((xs ⊕ ys) ⊕ zs)) ∣₁
  
    ⊕-comm : (xs ys : QFreeMon A) -> xs ⊕/ ys ≡ ys ⊕/ xs
    ⊕-comm =
      elimProp (λ _ -> isPropΠ (λ _ -> squash/ _ _)) λ xs ->
        elimProp (λ _ -> squash/ _ _) λ ys ->
          eq/ _ _ ∣ (r .⊕-commₚ) xs ys ∣₁
 
    qFreeMon-α : sig M.MonSig (QFreeMon A) -> QFreeMon A
    qFreeMon-α (M.`e , i) = Q.[ e ]
    qFreeMon-α (M.`⊕ , i) = i fzero ⊕/ i fone
  
    qFreeMon-sat : < QFreeMon A , qFreeMon-α > ⊨ M.CMonSEq
    qFreeMon-sat (M.`mon M.`unitl) ρ = ⊕-unitl (ρ fzero)
    qFreeMon-sat (M.`mon M.`unitr) ρ = ⊕-unitr (ρ fzero)
    qFreeMon-sat (M.`mon M.`assocr) ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)
    qFreeMon-sat M.`comm ρ = ⊕-comm (ρ fzero) (ρ fone)
 
  module IsFree {A : Type ℓr} {𝔜 : struct ℓB M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
    module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon
  
    𝔛 : M.CMonStruct
    𝔛 = < QFreeMon A , qFreeMon-α >
 
    module 𝔛 = M.CMonSEq 𝔛 qFreeMon-sat
 
    [_]-isMonHom : structHom 𝔉 𝔛
    fst [_]-isMonHom = Q.[_]
    snd [_]-isMonHom M.`e i = cong _/_.[_] 𝔉.e-eta
    snd [_]-isMonHom M.`⊕ i =
      𝔛 .alg (M.`⊕ , (λ x -> Q.[ i x ])) ≡⟨ 𝔛.⊕-eta i Q.[_] ⟩
      Q.[ freeMon .α (M.`⊕ , _) ] ≡⟨ cong (λ z -> Q.[_] {R = _≈ₚ_} (freeMon .α (M.`⊕ , z))) (lookup2≡i i) ⟩
      Q.[ freeMon .α (M.`⊕ , i) ] ∎
 
    module _ (f : A -> 𝔜 .car) where
      f♯ : structHom 𝔉 𝔜
      f♯ = ext (freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon) f
 
      _♯ : QFreeMon A -> 𝔜 .car    
      Q.[ as ] ♯ = f♯ .fst as 
      eq/ as bs p i ♯ = P.rec (isSet𝔜 _ _) (r .f-≅ₚ 𝔜-cmon f♯ as bs) p i
      squash/ xs ys p q i j ♯ = isSet𝔜 (xs ♯) (ys ♯) (cong _♯ p) (cong _♯ q) i j
 
      private
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
 
    private
      qFreeMonEquivLemma : (g : structHom 𝔛 𝔜) (x : 𝔛 .car) -> g .fst x ≡ ((g .fst ∘ η/) ♯) x
      qFreeMonEquivLemma g = elimProp (λ _ -> isSet𝔜 _ _) λ x i -> lemma (~ i) x
        where
        lemma : (f♯ (((g .fst) ∘ Q.[_]) ∘ freeMon .η)) .fst ≡ (g .fst) ∘ Q.[_]
        lemma = cong fst (ext-β (freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon) (structHom∘ 𝔉 𝔛 𝔜 g [_]-isMonHom))
 
    qFreeMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
    qFreeMonEquiv =
      isoToEquiv
        ( iso
          (λ g -> g .fst ∘ η/)
          ♯-isMonHom
          (ext-η (freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon))
          (λ g -> sym (structHom≡ 𝔛 𝔜 g (♯-isMonHom (g .fst ∘ η/)) isSet𝔜 (funExt (qFreeMonEquivLemma g))))
        )
  
module QFreeMonDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq
  
qFreeMonDef : ∀ {ℓ ℓ' : Level} {freeMon : Free ℓ ℓ' 2} -> PermRelation freeMon -> QFreeMonDef.Free ℓ ℓ' 2
F (qFreeMonDef rel) = QFreeMon.QFreeMon rel
η (qFreeMonDef rel) = QFreeMon.η/ rel
α (qFreeMonDef rel) = QFreeMon.qFreeMon-α rel
sat (qFreeMonDef rel) = QFreeMon.qFreeMon-sat rel
isFree (qFreeMonDef rel) isSet𝔜 satMon = (QFreeMon.IsFree.qFreeMonEquiv rel isSet𝔜 satMon) .snd
 