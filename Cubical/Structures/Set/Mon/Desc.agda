{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Structures.Set.Mon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.FinData as F public

open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str public
open import Cubical.Structures.Set.Tree
open import Cubical.Structures.Set.Eq

data MonSym : Type where
  e : MonSym
  ⊕ : MonSym

MonAr : MonSym -> Type
MonAr e = Fin 0
MonAr ⊕ = Fin 2

MonSig : Sig ℓ-zero ℓ-zero
Sig.symbol MonSig = MonSym
Sig.arity MonSig = MonAr

data MonEq : Type where
  unitl unitr assocr : MonEq

-- Vec n A ≃ Fin n -> A

MonEqFree : MonEq -> Type
MonEqFree unitl = Fin 1
MonEqFree unitr = Fin 1
MonEqFree assocr = Fin 3

MonEqLhs : (eq : MonEq) -> Tree MonSig (MonEqFree eq)
MonEqLhs unitl = node ⊕ (F.rec (node e \()) (leaf zero))
MonEqLhs unitr = node ⊕ (F.rec (leaf zero) (node e \()))
MonEqLhs assocr = node ⊕ (F.rec (node ⊕ (F.rec (leaf zero) (leaf (suc zero))))
                                (leaf (suc (suc zero))))

MonEqRhs : (eq : MonEq) -> Tree MonSig (MonEqFree eq)
MonEqRhs unitl = leaf zero
MonEqRhs unitr = leaf zero
MonEqRhs assocr = node ⊕ (F.rec (leaf zero)
                         (node ⊕ (F.rec (leaf (suc zero)) (leaf two))))

monEqLhs : (eq : MonEq) -> Tr MonSig (MonEqFree eq)
monEqLhs unitl = node (⊕ , rec (node (e , \())) (leaf zero))
monEqLhs unitr = node (⊕ , rec (leaf zero) (node (e , \())))
monEqLhs assocr = node (⊕ , rec (node (⊕ , rec (leaf zero) (leaf one))) (leaf two))

monEqRhs : (eq : MonEq) -> Tr MonSig (MonEqFree eq)
monEqRhs unitl = leaf zero
monEqRhs unitr = leaf zero
monEqRhs assocr = node (⊕ , rec (leaf zero) (node (⊕ , rec (leaf one) (leaf two))))

MonEqSig : EqSig ℓ-zero ℓ-zero
name MonEqSig = MonEq
free MonEqSig = MonEqFree

MonEqs : EqThy MonSig MonEqSig
lhs MonEqs = MonEqLhs
rhs MonEqs = MonEqRhs

MonSEq : seq MonSig MonEqSig
MonSEq n = monEqLhs n , monEqRhs n

MonStruct = Str ℓ-zero MonSig

module Examples where

  ℕ-MonStr : MonStruct
  Str.carrier ℕ-MonStr = ℕ
  Str.ops ℕ-MonStr e f = 0
  Str.ops ℕ-MonStr ⊕ f = f zero + f (suc zero)
  Str.isSetStr ℕ-MonStr = isSetℕ

  -- ℕ-MonStr-MonSEq : ℕ-MonStr ⊨ MonSEq
  -- ℕ-MonStr-MonSEq = ?
