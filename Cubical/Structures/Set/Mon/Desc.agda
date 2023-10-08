{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Desc where

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

data MonEq : Type where
  unitl unitr assocr : MonEq

MonEqFree : MonEq -> ℕ
MonEqFree unitl = 1
MonEqFree unitr = 1
MonEqFree assocr = 3

MonEqSig : EqSig ℓ-zero ℓ-zero
MonEqSig = finEqSig (MonEq , MonEqFree)

monEqLhs : (eq : MonEq) -> FinTree MonFinSig (MonEqFree eq)
monEqLhs unitl = node (⊕ , lookup (node (e , lookup []) ∷ leaf fzero ∷ []))
monEqLhs unitr = node (⊕ , lookup (leaf fzero ∷ node (e , lookup []) ∷ []))
monEqLhs assocr = node (⊕ , lookup (node (⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []))

monEqRhs : (eq : MonEq) -> FinTree MonFinSig (MonEqFree eq)
monEqRhs unitl = leaf fzero
monEqRhs unitr = leaf fzero
monEqRhs assocr = node (⊕ , lookup (leaf fzero ∷ node (⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []))

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
