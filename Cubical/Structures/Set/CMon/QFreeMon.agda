{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.QFreeMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q
open import Cubical.Data.List as L
open import Cubical.Relation.Binary

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

module _ {ℓ ℓ' : Level} (freeMon : Free ℓ ℓ' 2) where

  private
    ℱ : Type ℓ -> Type ℓ
    ℱ A = freeMon .F A

  PRel : Type ℓ -> Type (ℓ-max ℓ (ℓ-suc ℓ'))
  PRel A = Rel (ℱ A) (ℱ A) ℓ'

  record isPermRel {A : Type ℓ} (R : PRel A) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    constructor permRel
    infix 3 _≈_
    _≈_ : Rel (ℱ A) (ℱ A) ℓ' ; _≈_ = R
    -- TODO: Add ⊕ as a helper in Mon.Desc
    infixr 10 _⊕_
    _⊕_ : ℱ A -> ℱ A -> ℱ A
    a ⊕ b = freeMon .α (M.`⊕ , ⟪ a ⨾ b ⟫)
    module R = BinaryRelation R
    field
      isEquivRel : R.isEquivRel
      isCongruence : {a b c d : ℱ A}
                  -> a ≈ b -> c ≈ d
                  -> a ⊕ c ≈ b ⊕ d
      isCommutative : {a b : ℱ A}
                   -> a ⊕ b ≈ b ⊕ a
      resp-♯ : {a b : ℱ A} {𝔜 : struct ℓ' M.MonSig} {isSet𝔜 : isSet (𝔜 .car)} (𝔜-cmon : 𝔜 ⊨ M.CMonSEq)
            -> (f : A -> 𝔜 .car)
            -> a ≈ b
            -> let f♯ = ext freeMon isSet𝔜 (M.cmonSatMon 𝔜-cmon) f .fst in f♯ a ≡ f♯ b

    refl≈ = isEquivRel .R.isEquivRel.reflexive
    trans≈ = isEquivRel .R.isEquivRel.transitive
    cong≈ = isCongruence
    comm≈ = isCommutative
    subst≈-left : {a b c : ℱ A} -> a ≡ b -> a ≈ c -> b ≈ c
    subst≈-left {c = c} = subst (_≈ c)
    subst≈-right : {a b c : ℱ A} -> b ≡ c -> a ≈ b -> a ≈ c
    subst≈-right {a = a} = subst (a ≈_)
    subst≈ : {a b c d : ℱ A} -> a ≡ b -> c ≡ d -> a ≈ c -> b ≈ d
    subst≈ {a} {b} {c} {d} p q r = trans≈ b c d (subst≈-left p r) (subst≈-right q (refl≈ c))

  PermRelation : Type ℓ -> Type (ℓ-max ℓ (ℓ-suc ℓ'))
  PermRelation A = Σ (PRel A) isPermRel

module QFreeMon {ℓr ℓB} {freeMon : Free ℓr ℓB 2} (A : Type ℓr) ((R , isPermRelR) : PermRelation freeMon A) where
  private
    ℱ = freeMon .F A
  open isPermRel isPermRelR

  𝒬 : Type (ℓ-max ℓr ℓB)
  𝒬 = ℱ / _≈_

  𝔉 : M.MonStruct
  𝔉 = < ℱ , freeMon .α >

  module 𝔉 = M.MonSEq 𝔉 (freeMon .sat)

  e : ℱ
  e = 𝔉.e

  e/ : 𝒬
  e/ = Q.[ e ]

  η/ : A -> 𝒬
  η/ x = Q.[ freeMon .η x ]

  _⊕/_ : 𝒬 -> 𝒬 -> 𝒬
  _⊕/_ = Q.rec2 squash/
    (\a b -> Q.[ a ⊕ b ])
    (\a b c r -> eq/ (a ⊕ c) (b ⊕ c) (cong≈ r (refl≈ c)))
    (\a b c r -> eq/ (a ⊕ b) (a ⊕ c) (cong≈ (refl≈ a) r))

  ⊕-unitl : (a : 𝒬) -> e/ ⊕/ a ≡ a
  ⊕-unitl = Q.elimProp
    (\_ -> squash/ _ _)
    (\a -> eq/ (e ⊕ a) a (subst≈-right (𝔉.unitl a) (refl≈ (e ⊕ a))))

  ⊕-unitr : (a : 𝒬) -> a ⊕/ e/ ≡ a
  ⊕-unitr = Q.elimProp
    (\_ -> squash/ _ _)
    (\a -> eq/ (a ⊕ e) a (subst≈-right (𝔉.unitr a) (refl≈ (a ⊕ e))))

  ⊕-assocr : (a b c : 𝒬) -> (a ⊕/ b) ⊕/ c ≡ a ⊕/ (b ⊕/ c)
  ⊕-assocr = Q.elimProp
    (\_ -> isPropΠ (\_ -> isPropΠ (\_ -> squash/ _ _)))
    (\a -> elimProp
      (\_ -> isPropΠ (\_ -> squash/ _ _))
      (\b -> elimProp
        (\_ -> squash/ _ _)
        (\c -> eq/ ((a ⊕ b) ⊕ c) (a ⊕ (b ⊕ c)) (subst≈-right (𝔉.assocr a b c) (refl≈ ((a ⊕ b) ⊕ c))))))

  ⊕-comm : (a b : 𝒬) -> a ⊕/ b ≡ b ⊕/ a
  ⊕-comm = elimProp
    (\_ -> isPropΠ (\_ -> squash/ _ _))
    (\a -> elimProp
      (\_ -> squash/ _ _)
      (\b -> eq/ (a ⊕ b) (b ⊕ a) comm≈))

  qFreeMon-α : sig M.MonSig 𝒬 -> 𝒬
  qFreeMon-α (M.`e , i) = Q.[ e ]
  qFreeMon-α (M.`⊕ , i) = i fzero ⊕/ i fone

  qFreeMon-sat : < 𝒬 , qFreeMon-α > ⊨ M.CMonSEq
  qFreeMon-sat (M.`mon M.`unitl) ρ = ⊕-unitl (ρ fzero)
  qFreeMon-sat (M.`mon M.`unitr) ρ = ⊕-unitr (ρ fzero)
  qFreeMon-sat (M.`mon M.`assocr) ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)
  qFreeMon-sat M.`comm ρ = ⊕-comm (ρ fzero) (ρ fone)

  private
    𝔛 : M.CMonStruct
    𝔛 = < 𝒬 , qFreeMon-α >
    
    module 𝔛 = M.CMonSEq 𝔛 qFreeMon-sat

  [_]-isMonHom : structHom 𝔉 𝔛
  fst [_]-isMonHom = Q.[_]
  snd [_]-isMonHom M.`e i = cong _/_.[_] 𝔉.e-eta
  snd [_]-isMonHom M.`⊕ i =
    𝔛 .alg (M.`⊕ , (λ x -> Q.[ i x ])) ≡⟨ 𝔛.⊕-eta i Q.[_] ⟩
    Q.[ freeMon .α (M.`⊕ , _) ] ≡⟨ cong (λ z -> Q.[_] {R = _≈_} (freeMon .α (M.`⊕ , z))) (lookup2≡i i) ⟩
    Q.[ freeMon .α (M.`⊕ , i) ] ∎

  module IsFree {𝔜 : struct ℓB M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
    module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

    module _ (f : A -> 𝔜 .car) where
      f♯ : structHom 𝔉 𝔜
      f♯ = ext (freeMon) isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

      _♯ : 𝒬 -> 𝔜 .car
      _♯ = Q.rec isSet𝔜 (f♯ .fst) (\_ _ -> resp-♯ 𝔜-cmon f)

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

qFreeMonDef : ∀ {ℓ : Level} {freeMon : Free ℓ ℓ 2} (R : {A : Type ℓ} -> PermRelation freeMon A) -> QFreeMonDef.Free ℓ ℓ 2
F (qFreeMonDef R) A = QFreeMon.𝒬 A R
η (qFreeMonDef R) = QFreeMon.η/ _ R
α (qFreeMonDef R) = QFreeMon.qFreeMon-α _ R
sat (qFreeMonDef R) = QFreeMon.qFreeMon-sat _ R
isFree (qFreeMonDef R) isSet𝔜 𝔜-cmon = (QFreeMon.IsFree.qFreeMonEquiv _ R isSet𝔜 𝔜-cmon) .snd
