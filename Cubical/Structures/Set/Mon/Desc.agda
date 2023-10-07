{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.List

open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str public
open import Cubical.Structures.Set.Tree
open import Cubical.Structures.Set.Eq
open import Cubical.Structures.Arity as F

data MonSym : Type where
  e : MonSym
  ⊕ : MonSym

MonAr : MonSym -> Type
MonAr e = Arity 0
MonAr ⊕ = Arity 2

MonSig : Sig ℓ-zero ℓ-zero
Sig.symbol MonSig = MonSym
Sig.arity MonSig = MonAr

data MonEq : Type where
  unitl unitr assocr : MonEq

-- Vec n A ≃ Fin n -> A

MonEqFree : MonEq -> Type
MonEqFree unitl = Arity 1
MonEqFree unitr = Arity 1
MonEqFree assocr = Arity 3

monEqLhs : (eq : MonEq) -> Tree MonSig (MonEqFree eq)
monEqLhs unitl  = node (⊕ , lookup (node (e , fabsurd) ∷ leaf fzero ∷ []))
monEqLhs unitr  = node (⊕ , lookup (leaf fzero ∷ node (e , fabsurd) ∷ []))
monEqLhs assocr = node (⊕ , lookup ((node (⊕ , lookup (leaf fzero ∷ leaf fone ∷ []))) ∷ leaf ftwo ∷ []))

monEqRhs : (eq : MonEq) -> Tree MonSig (MonEqFree eq)
monEqRhs unitl = leaf fzero
monEqRhs unitr = leaf fzero
monEqRhs assocr = node (⊕ , lookup (leaf fzero ∷ node (⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []))

MonEqSig : EqSig ℓ-zero ℓ-zero
name MonEqSig = MonEq
free MonEqSig = MonEqFree

MonSEq : seq MonSig MonEqSig
MonSEq n = monEqLhs n , monEqRhs n

MonStruct : ∀ {n : Level} -> Type (ℓ-suc n)
MonStruct {n} = struct n MonSig

module Examples where

  ℕ-MonStr : MonStruct
  carrier ℕ-MonStr = ℕ
  algebra ℕ-MonStr (e , _) = 0
  algebra ℕ-MonStr (⊕ , i) = i fzero + i fone

  ℕ-MonStr-MonSEq : ℕ-MonStr ⊨ MonSEq
  ℕ-MonStr-MonSEq unitl ρ = refl
  ℕ-MonStr-MonSEq unitr ρ = +-zero (ρ fzero)
  ℕ-MonStr-MonSEq assocr ρ = sym (+-assoc (ρ fzero) (ρ fone) (ρ ftwo))
