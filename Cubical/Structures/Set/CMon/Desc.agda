{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Structures.Set.CMon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Structures.Arity as F public

open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq

import Cubical.Structures.Set.Mon.Desc as M
open M.MonSym

CMonSym = M.MonSym
CMonAr = M.MonAr
CMonFinSig = M.MonFinSig
CMonSig = M.MonSig

data CMonEq : Type where
  unitl unitr assocr comm : CMonEq

CMonEqFree : CMonEq -> ℕ
CMonEqFree unitl = 1
CMonEqFree unitr = 1
CMonEqFree assocr = 3
CMonEqFree comm = 2

CMonEqSig : EqSig ℓ-zero ℓ-zero
CMonEqSig = finEqSig (CMonEq , CMonEqFree)

cmonEqLhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqLhs unitl = node (⊕ , lookup (node (e , lookup []) ∷ leaf fzero ∷ []))
cmonEqLhs unitr = node (⊕ , lookup (leaf fzero ∷ node (e , lookup []) ∷ []))
cmonEqLhs assocr = node (⊕ , lookup (node (⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []))
cmonEqLhs comm = node (⊕ , lookup (leaf fzero ∷ leaf fone ∷ []))

cmonEqRhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqRhs unitl = leaf fzero
cmonEqRhs unitr = leaf fzero
cmonEqRhs assocr = node (⊕ , lookup (leaf fzero ∷ node (⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []))
cmonEqRhs comm = node (⊕ , lookup (leaf fone ∷ leaf fzero ∷ []))

CMonSEq : seq CMonSig CMonEqSig
CMonSEq n = cmonEqLhs n , cmonEqRhs n

CMonStruct : {n : Level} -> Type (ℓ-suc n)
CMonStruct {n} = struct n CMonSig

cmonSatMon : ∀ {s} {str : struct s CMonSig} -> str ⊨ CMonSEq -> str ⊨ M.MonSEq
cmonSatMon {_} {str} cmonSat M.unitl ρ = cmonSat unitl ρ
cmonSatMon {_} {str} cmonSat M.unitr ρ = cmonSat unitr ρ
cmonSatMon {_} {str} cmonSat M.assocr ρ = cmonSat assocr ρ

module Examples where

  ℕ-CMonStr : CMonStruct
  ℕ-CMonStr = M.Examples.ℕ-MonStr

  ℕ-CMonStr-MonSEq : ℕ-CMonStr ⊨ CMonSEq
  ℕ-CMonStr-MonSEq unitl ρ = refl
  ℕ-CMonStr-MonSEq unitr ρ = +-zero (ρ fzero)
  ℕ-CMonStr-MonSEq assocr ρ = sym (+-assoc (ρ fzero) (ρ fone) (ρ ftwo))
  ℕ-CMonStr-MonSEq comm ρ = +-comm (ρ fzero) (ρ fone)
