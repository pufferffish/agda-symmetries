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

MonSEq : seq MonSig MonEqSig
MonSEq n = monEqLhs n , monEqRhs n

MonStruct : ∀ {n : Level} -> Type (ℓ-suc n)
MonStruct {n} = struct {ℓ-zero} {ℓ-zero} {n} MonSig

module Examples where

  ℕ-MonStr : MonStruct
  carrier ℕ-MonStr = ℕ
  algebra ℕ-MonStr (e , _) = 0
  algebra ℕ-MonStr (⊕ , i) = i zero + i one

  ℕ-MonStr-MonSEq : ℕ-MonStr ⊨ MonSEq
  ℕ-MonStr-MonSEq unitl ρ = refl
  ℕ-MonStr-MonSEq unitr ρ = +-zero (ρ zero)
  ℕ-MonStr-MonSEq assocr ρ = sym (+-assoc (ρ zero) (ρ one) (ρ two))
