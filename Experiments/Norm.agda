{-# OPTIONS --cubical --safe --exact-split #-}

open import Agda.Primitive

-- TODO: Fix levels in Free so this isn't necessary
module Experiments.Norm {ℓ : Level} {A : Set ℓ} where

open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum as ⊎
open import Cubical.Induction.WellFounded
import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SetQuotients as Q

import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F

open import Cubical.Structures.Set.CMon.Free as F
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Structures.Set.CMon.Bag
open import Cubical.Structures.Set.CMon.SList as S

module CMonDef = F.Definition M.CMonSig M.CMonEqSig M.CMonSEq

module FCM = CMonDef.Free

ηᵇ : A -> Bag A
ηᵇ = FCM.η bagFreeDef

ηˢ : A -> SList A
ηˢ = FCM.η {ℓ' = ℓ} slistDef

ηˢ♯ : structHom < Bag A , FCM.α bagFreeDef > < SList A , FCM.α {ℓ' = ℓ} slistDef >
ηˢ♯ = FCM.ext bagFreeDef S.isSetSList (FCM.sat {ℓ' = ℓ} S.slistDef) ηˢ

ηᵇ♯ : structHom < SList A , FCM.α {ℓ' = ℓ} slistDef > < Bag A , FCM.α bagFreeDef >
ηᵇ♯ = FCM.ext slistDef Q.squash/ (FCM.sat bagFreeDef) (FCM.η bagFreeDef)

ηᵇ♯∘ηˢ♯ : structHom < Bag A , FCM.α bagFreeDef > < Bag A , FCM.α bagFreeDef >
ηᵇ♯∘ηˢ♯ = structHom∘ < Bag _ , FCM.α bagFreeDef > < SList _ , FCM.α {ℓ' = ℓ} slistDef > < Bag _ , FCM.α bagFreeDef > ηᵇ♯ ηˢ♯

ηᵇ♯∘ηˢ♯-β : ηᵇ♯∘ηˢ♯ .fst ∘ ηᵇ ≡ ηᵇ
ηᵇ♯∘ηˢ♯-β =
    ηᵇ♯ .fst ∘ ηˢ♯ .fst ∘ ηᵇ
  ≡⟨ cong (ηᵇ♯ .fst ∘_) (FCM.ext-η bagFreeDef S.isSetSList (FCM.sat {ℓ' = ℓ} slistDef) ηˢ) ⟩
    ηᵇ♯ .fst ∘ ηˢ
  ≡⟨ FCM.ext-η slistDef Q.squash/ (FCM.sat bagFreeDef) ηᵇ ⟩
    ηᵇ
  ∎

ηᵇ♯∘ηˢ♯-η : ηᵇ♯∘ηˢ♯ ≡ idHom < Bag A , FCM.α bagFreeDef >
ηᵇ♯∘ηˢ♯-η = FCM.hom≡ bagFreeDef Q.squash/ (FCM.sat bagFreeDef) ηᵇ♯∘ηˢ♯ (idHom _) ηᵇ♯∘ηˢ♯-β

𝔫𝔣 : Bag A -> SList A
𝔫𝔣 = ηˢ♯ .fst

𝔫𝔣-inj : {as bs : Bag A} -> 𝔫𝔣 as ≡ 𝔫𝔣 bs -> as ≡ bs
𝔫𝔣-inj {as} {bs} p = sym (funExt⁻ (cong fst ηᵇ♯∘ηˢ♯-η) as) ∙ cong (ηᵇ♯ .fst) p ∙ funExt⁻ (cong fst ηᵇ♯∘ηˢ♯-η) bs

norm : isEmbedding 𝔫𝔣
norm = injEmbedding isSetSList 𝔫𝔣-inj

-- also equivalence
