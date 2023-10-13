{-# OPTIONS --cubical #-}

module Cubical.Structures.Gpd.SMon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.List

open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity as F

data MonSym : Type where
  e : MonSym
  ⊕ : MonSym

MonAr : MonSym -> ℕ
MonAr e = 0
MonAr ⊕ = 2

MonFinSig : FinSig ℓ-zero
MonFinSig = MonSym , MonAr

MonSig : Sig ℓ-zero ℓ-zero
MonSig = finSig MonFinSig

data SMonEq : Type where
  unitl unitr assocr symm : SMonEq

SMonEqFree : SMonEq -> ℕ
SMonEqFree unitl = 1
SMonEqFree unitr = 1
SMonEqFree assocr = 3
SMonEqFree symm = 2

SMonEqSig : EqSig ℓ-zero ℓ-zero
SMonEqSig = finEqSig (SMonEq , SMonEqFree)

smonEqLhs : (eq : SMonEq) -> FinTree MonFinSig (SMonEqFree eq)
smonEqLhs unitl = node (⊕ , lookup (node (e , lookup []) ∷ leaf fzero ∷ []))
smonEqLhs unitr = node (⊕ , lookup (leaf fzero ∷ node (e , lookup []) ∷ []))
smonEqLhs assocr = node (⊕ , lookup (node (⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []))
smonEqLhs symm = node (⊕ , lookup (leaf fzero ∷ leaf fone ∷ []))

smonEqRhs : (eq : SMonEq) -> FinTree MonFinSig (SMonEqFree eq)
smonEqRhs unitl = leaf fzero
smonEqRhs unitr = leaf fzero
smonEqRhs assocr = node (⊕ , lookup (leaf fzero ∷ node (⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []))
smonEqRhs symm = node (⊕ , lookup (leaf fone ∷ leaf fzero ∷ []))

SMonSEq : seq MonSig SMonEqSig
SMonSEq n = smonEqLhs n , smonEqRhs n

SMonStruct : ∀ {n : Level} -> Type (ℓ-suc n)
SMonStruct {n} = struct n MonSig

-- module Examples where
-- 
--   ℕ-MonStr : MonStruct
--   carrier ℕ-MonStr = ℕ
--   algebra ℕ-MonStr (e , _) = 0
--   algebra ℕ-MonStr (⊕ , i) = i fzero + i fone
-- 
--   ℕ-MonStr-MonSEq : ℕ-MonStr ⊨ MonSEq
--   ℕ-MonStr-MonSEq unitl ρ = refl
--   ℕ-MonStr-MonSEq unitr ρ = +-zero (ρ fzero)
--   ℕ-MonStr-MonSEq assocr ρ = sym (+-assoc (ρ fzero) (ρ fone) (ρ ftwo))
-- 
-- 