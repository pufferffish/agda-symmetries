{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.PList where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon

data Perm {ℓ : Level} {A : Type ℓ} : List A -> List A -> Type ℓ where
  perm-refl : ∀ {xs} -> Perm xs xs
  perm-swap : ∀ {x y xs ys zs} -> Perm (xs ++ x ∷ y ∷ ys) zs -> Perm (xs ++ y ∷ x ∷ ys) zs 

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

infixr 30 _∙ₚ_
_∙ₚ_ : ∀ {xs ys zs} -> Perm xs ys -> Perm ys zs -> Perm {A = A} xs zs
perm-refl ∙ₚ q = q
(perm-swap p) ∙ₚ q = perm-swap (p ∙ₚ q)

perm-sym : ∀ {xs ys} -> Perm xs ys -> Perm {A = A} ys xs
perm-sym perm-refl = perm-refl
perm-sym (perm-swap p) = perm-sym p ∙ₚ perm-swap perm-refl

perm-subst : ∀ {xs ys} -> xs ≡ ys -> Perm {A = A} xs ys
perm-subst {xs = xs} p = subst (Perm xs) p perm-refl

perm-∷ : ∀ {x xs ys} -> Perm xs ys -> Perm {A = A} (x ∷ xs) (x ∷ ys)
perm-∷ perm-refl = perm-refl
perm-∷ {x = x} (perm-swap {xs = xs} p) = perm-swap {xs = x ∷ xs} (perm-∷ p)

perm-prepend : (xs : List A) {ys zs : List A} -> Perm ys zs -> Perm (xs ++ ys) (xs ++ zs)
perm-prepend [] p = p
perm-prepend (x ∷ xs) p = perm-∷ (perm-prepend xs p)

perm-append : ∀ {xs ys} -> Perm xs ys -> (zs : List A) -> Perm (xs ++ zs) (ys ++ zs)
perm-append perm-refl _ = perm-refl
perm-append (perm-swap {xs = xs} p) _ =
  perm-subst (++-assoc xs _ _) ∙ₚ perm-swap (perm-subst (sym (++-assoc xs _ _)) ∙ₚ perm-append p _)

perm-movehead : (x : A) (xs : List A) {ys : List A} -> Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
perm-movehead x [] = perm-refl
perm-movehead x (y ∷ xs) = perm-swap {xs = []} (perm-∷ (perm-movehead x xs))

⊕-commₚ : (xs ys : List A) -> Perm (xs ++ ys) (ys ++ xs)
⊕-commₚ xs [] = perm-subst (++-unit-r xs)
⊕-commₚ xs (y ∷ ys) = perm-sym (perm-movehead y xs {ys = ys}) ∙ₚ perm-∷ (⊕-commₚ xs ys)

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f-hom : structHom < List A , LM.list-α > 𝔜) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f : List A -> 𝔜 .car
  f = f-hom .fst

  f-++ : ∀ xs ys -> f (xs ++ ys) ≡ f xs 𝔜.⊕ f ys
  f-++ xs ys =
    f (xs ++ ys) ≡⟨ sym ((f-hom .snd) M.`⊕ (lookup (xs ∷ ys ∷ []))) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f (lookup (xs ∷ ys ∷ []) w))) ≡⟨ 𝔜.⊕-eta (lookup (xs ∷ ys ∷ [])) f ⟩
    _ ∎

  f-≅ₚ-α : ∀ {x y : A} (xs ys : List A) -> f (xs ++ x ∷ y ∷ ys) ≡ f (xs ++ y ∷ x ∷ ys)
  f-≅ₚ-α {x} {y} [] ys =
    f ((L.[ x ] ++ L.[ y ]) ++ ys) ≡⟨ f-++ (L.[ x ] ++ L.[ y ]) ys  ⟩
    f (L.[ x ] ++ L.[ y ]) 𝔜.⊕ f ys ≡⟨ cong (𝔜._⊕ f ys) (f-++ L.[ x ] L.[ y ]) ⟩
    (f L.[ x ] 𝔜.⊕ f L.[ y ]) 𝔜.⊕ f ys ≡⟨ cong (𝔜._⊕ f ys) (𝔜.comm _ _) ⟩
    (f L.[ y ] 𝔜.⊕ f L.[ x ]) 𝔜.⊕ f ys ≡⟨ cong (𝔜._⊕ f ys) (sym (f-++ L.[ y ] L.[ x ])) ⟩
    f (L.[ y ] ++ L.[ x ]) 𝔜.⊕ f ys ≡⟨ sym (f-++ (L.[ y ] ++ L.[ x ]) ys) ⟩
    f ((L.[ y ] ++ L.[ x ]) ++ ys) ∎
  f-≅ₚ-α {x} {y} (a ∷ as) ys =
    f (L.[ a ] ++ (as ++ x ∷ y ∷ ys)) ≡⟨ f-++ L.[ a ] (as ++ x ∷ y ∷ ys) ⟩
    f L.[ a ] 𝔜.⊕ f (as ++ x ∷ y ∷ ys) ≡⟨ cong (f L.[ a ] 𝔜.⊕_) (f-≅ₚ-α as ys) ⟩
    f L.[ a ] 𝔜.⊕ f (as ++ y ∷ x ∷ ys) ≡⟨ sym (f-++ L.[ a ] (as ++ y ∷ x ∷ ys)) ⟩
    f (L.[ a ] ++ (as ++ y ∷ x ∷ ys)) ≡⟨⟩
    f ((a ∷ as) ++ y ∷ x ∷ ys) ∎

  f-≅ₚ : ∀ {xs zs} -> Perm xs zs -> f xs ≡ f zs
  f-≅ₚ perm-refl = refl
  f-≅ₚ (perm-swap {xs = xs} p) = f-≅ₚ-α xs _ ∙ f-≅ₚ p

permRelation : ∀ {ℓ ℓ'} -> PermRelation {ℓ} {ℓ'} LM.listDef
PermRelation.R permRelation = Perm
PermRelation.perm-refl permRelation as = perm-refl
PermRelation.perm-append permRelation as bs p cs = perm-append p cs
PermRelation.perm-prepend permRelation bs cs as p = perm-prepend as p
PermRelation.⊕-commₚ permRelation = ⊕-commₚ
PermRelation.f-≅ₚ permRelation 𝔜-cmon f xs zs r = f-≅ₚ 𝔜-cmon f r

module PListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

plistFreeDef : ∀ {ℓ ℓ'} -> PListDef.Free ℓ ℓ' 2
plistFreeDef = qFreeMonDef permRelation