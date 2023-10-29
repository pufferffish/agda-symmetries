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

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} {isSet𝔜 : isSet (𝔜 .car)} (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f : A -> 𝔜 .car) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f♯-hom = LM.Free.♯-isMonHom isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

  f♯ : List A -> 𝔜 .car
  f♯ = f♯-hom .fst

  f♯-++ : ∀ xs ys -> f♯ (xs ++ ys) ≡ f♯ xs 𝔜.⊕ f♯ ys
  f♯-++ xs ys =
    f♯ (xs ++ ys) ≡⟨ sym ((f♯-hom .snd) M.`⊕ (lookup (xs ∷ ys ∷ []))) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f♯ (lookup (xs ∷ ys ∷ []) w))) ≡⟨ 𝔜.⊕-eta (lookup (xs ∷ ys ∷ [])) f♯ ⟩
    _ ∎

  f♯-swap : ∀ {x y : A} (xs ys : List A) -> f♯ (xs ++ x ∷ y ∷ ys) ≡ f♯ (xs ++ y ∷ x ∷ ys)
  f♯-swap {x} {y} [] ys =
    f♯ ((L.[ x ] ++ L.[ y ]) ++ ys) ≡⟨ f♯-++ (L.[ x ] ++ L.[ y ]) ys  ⟩
    f♯ (L.[ x ] ++ L.[ y ]) 𝔜.⊕ f♯ ys ≡⟨ cong (𝔜._⊕ f♯ ys) (f♯-++ L.[ x ] L.[ y ]) ⟩
    (f♯ L.[ x ] 𝔜.⊕ f♯ L.[ y ]) 𝔜.⊕ f♯ ys ≡⟨ cong (𝔜._⊕ f♯ ys) (𝔜.comm _ _) ⟩
    (f♯ L.[ y ] 𝔜.⊕ f♯ L.[ x ]) 𝔜.⊕ f♯ ys ≡⟨ cong (𝔜._⊕ f♯ ys) (sym (f♯-++ L.[ y ] L.[ x ])) ⟩
    f♯ (L.[ y ] ++ L.[ x ]) 𝔜.⊕ f♯ ys ≡⟨ sym (f♯-++ (L.[ y ] ++ L.[ x ]) ys) ⟩
    f♯ ((L.[ y ] ++ L.[ x ]) ++ ys) ∎
  f♯-swap {x} {y} (a ∷ as) ys =
    f♯ (L.[ a ] ++ (as ++ x ∷ y ∷ ys)) ≡⟨ f♯-++ L.[ a ] (as ++ x ∷ y ∷ ys) ⟩
    f♯ L.[ a ] 𝔜.⊕ f♯ (as ++ x ∷ y ∷ ys) ≡⟨ cong (f♯ L.[ a ] 𝔜.⊕_) (f♯-swap as ys) ⟩
    f♯ L.[ a ] 𝔜.⊕ f♯ (as ++ y ∷ x ∷ ys) ≡⟨ sym (f♯-++ L.[ a ] (as ++ y ∷ x ∷ ys)) ⟩
    f♯ (L.[ a ] ++ (as ++ y ∷ x ∷ ys)) ≡⟨⟩
    f♯ ((a ∷ as) ++ y ∷ x ∷ ys) ∎

  perm-resp-f♯ : {a b : List A} -> Perm a b -> f♯ a ≡ f♯ b
  perm-resp-f♯ perm-refl = refl
  perm-resp-f♯ (perm-swap {xs = xs} {ys = ys} p) = f♯-swap xs ys ∙ perm-resp-f♯ p

module _ {ℓ} (A : Type ℓ) where
  open import Cubical.Relation.Binary
  module P = BinaryRelation {A = List A} Perm
  open isPermRel

  isPermRelPerm : isPermRel LM.listDef (Perm {A = A})
  P.isEquivRel.reflexive (isEquivRel isPermRelPerm) _ = perm-refl
  P.isEquivRel.symmetric (isEquivRel isPermRelPerm) _ _ = perm-sym
  P.isEquivRel.transitive (isEquivRel isPermRelPerm) _ _ _ = _∙ₚ_
  isCongruence isPermRelPerm {a} {b} {c} {d} p q = perm-prepend a q ∙ₚ perm-append p d
  isCommutative isPermRelPerm {a} {b} = ⊕-commₚ a b
  resp-♯ isPermRelPerm {isSet𝔜 = isSet𝔜} 𝔜-cmon f p = perm-resp-f♯ {isSet𝔜 = isSet𝔜} 𝔜-cmon f p

  PermRel : PermRelation LM.listDef A
  PermRel = Perm , isPermRelPerm

module PListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

plistFreeDef : ∀ {ℓ} -> PListDef.Free ℓ ℓ 2
plistFreeDef = qFreeMonDef (PermRel _)
