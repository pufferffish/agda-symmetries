{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.FinData as F public

open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str public
open import Cubical.Structures.Set.Tree
open import Cubical.Structures.Set.Eq

data CMonSym : Type where
  e : CMonSym
  ⊕ : CMonSym

CMonAr : CMonSym -> Type
CMonAr e = Fin 0
CMonAr ⊕ = Fin 2

CMonSig : Sig ℓ-zero ℓ-zero
Sig.symbol CMonSig = CMonSym
Sig.arity CMonSig = CMonAr

data CMonEq : Type where
  unitl unitr assocr comm : CMonEq

-- Vec n A ≃ Fin n -> A

CMonEqFree : CMonEq -> Type
CMonEqFree unitl = Fin 1
CMonEqFree unitr = Fin 1
CMonEqFree assocr = Fin 3
CMonEqFree comm = Fin 2

CMonEqLhs : (eq : CMonEq) -> Tree CMonSig (CMonEqFree eq)
CMonEqLhs unitl = node ⊕ (F.rec (node e \()) (leaf zero))
CMonEqLhs unitr = node ⊕ (F.rec (leaf zero) (node e \()))
CMonEqLhs assocr = node ⊕ (F.rec (node ⊕ (F.rec (leaf zero) (leaf (suc zero))))
                                (leaf (suc (suc zero))))
CMonEqLhs comm = {!!} -- TODO: comm equation

CMonEqRhs : (eq : CMonEq) -> Tree CMonSig (CMonEqFree eq)
CMonEqRhs unitl = leaf zero
CMonEqRhs unitr = leaf zero
CMonEqRhs assocr = node ⊕ (F.rec (leaf zero)
                         (node ⊕ (F.rec (leaf (suc zero)) (leaf two))))
CMonEqRhs comm = {!!}

CMonEqSig : EqSig ℓ-zero ℓ-zero
name CMonEqSig = CMonEq
free CMonEqSig = CMonEqFree

CMonEqs : EqThy CMonSig CMonEqSig
lhs CMonEqs = CMonEqLhs
rhs CMonEqs = CMonEqRhs

CMonSEq : seq CMonSig CMonEqSig
CMonSEq n = {!!} , {!!} -- TODO: Tr vs Tree

CMonStruct = Str ℓ-zero CMonSig

module Examples where

  ℕ-CMonStr : CMonStruct
  Str.carrier ℕ-CMonStr = ℕ
  Str.ops ℕ-CMonStr e f = 0
  Str.ops ℕ-CMonStr ⊕ f = f zero + f (suc zero)
  Str.isSetStr ℕ-CMonStr = isSetℕ

  -- ℕ-CMonStr-CMonSeq : ℕ-CMonStr ⊨ CMonSEq -- TODO: struct vs Str
  -- ℕ-CMonStr-MoNSEq = ?
