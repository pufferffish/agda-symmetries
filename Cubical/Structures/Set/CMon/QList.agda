{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.QList where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List as L
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)

record PermRelation : Typeω where
  field
    R : ∀ {ℓ} {A : Type ℓ} -> List A -> List A -> Type ℓ

    perm-append : ∀ {ℓ} {A : Type ℓ} (as bs : List A) -> (p : R as bs) -> (cs : List A) -> R (as ++ cs) (bs ++ cs)
    perm-prepend : ∀ {ℓ} {A : Type ℓ} (bs cs : List A) -> (as : List A) -> (p : R bs cs) -> R (as ++ bs) (as ++ cs)

    ⊕-unitlₚ : ∀ {ℓ} {A : Type ℓ} -> (as : List A) -> R ([] ++ as) as
    ⊕-unitrₚ : ∀ {ℓ} {A : Type ℓ} -> (as : List A) -> R (as ++ []) as
    ⊕-assocrₚ : ∀ {ℓ} {A : Type ℓ} -> (as bs cs : List A) -> R ((as ++ bs) ++ cs) (as ++ (bs ++ cs))
    ⊕-commₚ : ∀ {ℓ} {A : Type ℓ} -> (xs ys : List A) -> R (xs ++ ys) (ys ++ xs)

    f-≅ₚ : ∀ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig}
      (𝔜-cmon : 𝔜 ⊨ M.CMonSEq)
      (f : structHom < List A , LM.list-α > 𝔜)
      (xs zs : List A)
      -> R xs zs -> (f .fst) xs ≡ (f .fst) zs

module QListFree (r : PermRelation) where
  open PermRelation

  private
    variable
      ℓ : Level
      A B : Type ℓ

  _≈ₚ_ : ∀ {A : Type ℓ} -> List A -> List A -> Type ℓ
  xs ≈ₚ ys = ∥ (r .R) xs ys ∥₁

  QList : Type ℓ -> Type ℓ
  QList A = List A / _≈ₚ_

  e : QList A
  e = Q.[ [] ]
  
  η : A -> QList A
  η x = Q.[ x ∷ [] ]
  
  _⊕_ : QList A -> QList A -> QList A
  _⊕_ = Q.rec2 squash/
    (λ xs ys -> Q.[ xs ++ ys ])
    (λ as bs cs p -> eq/ (as ++ cs) (bs ++ cs) (P.map (λ p -> (r .perm-append as bs) p cs) p))
    (λ as bs cs p -> eq/ (as ++ bs) (as ++ cs) (P.map (λ p -> (r .perm-prepend bs cs) as p) p))

  ⊕-unitl : (as : QList A) -> e ⊕ as ≡ as
  ⊕-unitl = elimProp (λ _ -> squash/ _ _) (λ as -> eq/ _ _ ∣  (r .⊕-unitlₚ) as ∣₁)

  ⊕-unitr : (as : QList A) -> as ⊕ e ≡ as
  ⊕-unitr = elimProp (λ _ -> squash/ _ _) (λ as -> eq/ _ _ ∣ (r .⊕-unitrₚ) as ∣₁)

  ⊕-assocr : (as bs cs : QList A) -> (as ⊕ bs) ⊕ cs ≡ as ⊕ (bs ⊕ cs)
  ⊕-assocr =
    elimProp (λ _ -> isPropΠ (λ _ -> isPropΠ (λ _ -> squash/ _ _))) λ xs ->
      elimProp (λ _ -> isPropΠ λ _ -> squash/ _ _) λ ys ->
        elimProp (λ _ -> squash/ _ _) λ zs ->
          eq/ _ _ ∣ (r .⊕-assocrₚ) xs ys zs ∣₁
  
  ⊕-comm : (xs ys : QList A) -> xs ⊕ ys ≡ ys ⊕ xs
  ⊕-comm =
    elimProp (λ _ -> isPropΠ (λ _ -> squash/ _ _)) λ xs ->
      elimProp (λ _ -> squash/ _ _) λ ys ->
        eq/ _ _ ∣ (r .⊕-commₚ) xs ys ∣₁

  qlist-α : ∀ {X : Type ℓ} -> sig M.MonSig (QList X) -> QList X
  qlist-α (M.`e , i) = Q.[ [] ]
  qlist-α (M.`⊕ , i) = i fzero ⊕ i fone
  
  module Free {y : Level} {A : Type ℓ} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
    module 𝔜' = M.CMonSEq 𝔜 𝔜-cmon
    open LM.Free {A = A} isSet𝔜 (M.cmonSatMon 𝔜-cmon)
  
    𝔛 : M.CMonStruct
    𝔛 = < QList A , qlist-α >
  
    module _ (f : A -> 𝔜 .car) where
      _♯ₚ : QList A -> 𝔜 .car    
      Q.[ as ] ♯ₚ = (f ♯) as
      eq/ as bs p i ♯ₚ = P.rec (isSet𝔜 _ _) (r .f-≅ₚ 𝔜-cmon (♯-isMonHom f) as bs) p i
      squash/ xs ys p q i j ♯ₚ = isSet𝔜 (xs ♯ₚ) (ys ♯ₚ) (cong _♯ₚ p) (cong _♯ₚ q) i j
  
      ♯ₚ-++ : ∀ xs ys -> (xs ⊕ ys) ♯ₚ ≡ (xs ♯ₚ) 𝔜.⊕ (ys ♯ₚ)
      ♯ₚ-++ =
        elimProp (λ _ -> isPropΠ λ _ -> isSet𝔜 _ _) λ xs ->
          elimProp (λ _ -> isSet𝔜 _ _) λ ys ->
            ♯-++ f xs ys
  
      ♯ₚ-isMonHom : structHom 𝔛 𝔜
      fst ♯ₚ-isMonHom = _♯ₚ
      snd ♯ₚ-isMonHom M.`e i = 𝔜.e-eta
      snd ♯ₚ-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ₚ ∙ sym (♯ₚ-++ (i fzero) (i fone))
  
    private
      qlistEquivLemma : (g : structHom 𝔛 𝔜) -> (x : QList A) -> g .fst x ≡ ((g .fst ∘ η) ♯ₚ) x
      qlistEquivLemma (g , homMonWit) = elimProp (λ _ -> isSet𝔜 _ _) lemma
        where
        lemma : (a : List A) -> g Q.[ a ] ≡ ((g ∘ η) ♯) a
        lemma [] = sym (homMonWit M.`e (lookup L.[])) ∙ 𝔜.e-eta
        lemma (a ∷ as) =
          g Q.[ a ∷ as ] ≡⟨ sym (homMonWit M.`⊕ (lookup (Q.[ L.[ a ] ] ∷ Q.[ as ] ∷ L.[]))) ⟩
          _ ≡⟨ 𝔜.⊕-eta (lookup (Q.[ L.[ a ] ] ∷ Q.[ as ] ∷ L.[])) g ⟩
          _ ≡⟨ cong (g Q.[ L.[ a ] ] 𝔜.⊕_) (lemma as) ⟩
          _ ∎
  
      qlistEquivLemma-β : (g : structHom 𝔛 𝔜) -> g ≡ ♯ₚ-isMonHom (g .fst ∘ η)
      qlistEquivLemma-β g = structHom≡ 𝔛 𝔜 g (♯ₚ-isMonHom (g .fst ∘ η)) isSet𝔜 (funExt (qlistEquivLemma g))
  
    qlistMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
    qlistMonEquiv =
      isoToEquiv (iso (λ g -> g .fst ∘ η) ♯ₚ-isMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ qlistEquivLemma-β))
  
  module QListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq
  
  qlist-sat : ∀ {X : Type ℓ} -> < QList X , qlist-α > ⊨ M.CMonSEq
  qlist-sat (M.`mon M.`unitl) ρ = ⊕-unitl (ρ fzero)
  qlist-sat (M.`mon M.`unitr) ρ = ⊕-unitr (ρ fzero)
  qlist-sat (M.`mon M.`assocr) ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)
  qlist-sat M.`comm ρ = ⊕-comm (ρ fzero) (ρ fone)
  
  qlistDef : QListDef.Free 2
  F.Definition.Free.F qlistDef = QList
  F.Definition.Free.η qlistDef = η
  F.Definition.Free.α qlistDef = qlist-α
  F.Definition.Free.sat qlistDef = qlist-sat
  F.Definition.Free.isFree qlistDef isSet𝔜 satMon = (Free.qlistMonEquiv isSet𝔜 satMon) .snd
 