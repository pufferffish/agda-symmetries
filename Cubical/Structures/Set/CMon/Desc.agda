{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Structures.Set.CMon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
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

CMonStruct : ∀ {n} -> Type (ℓ-suc n)
CMonStruct {n} = struct n CMonSig

CMon→Mon : ∀ {ℓ} -> CMonStruct {ℓ} -> M.MonStruct {ℓ}
carrier (CMon→Mon 𝔛) = 𝔛 .carrier
algebra (CMon→Mon 𝔛) = 𝔛 .algebra

module CMonStruct {ℓ} (𝔛 : CMonStruct {ℓ}) where
  open M.MonStruct (CMon→Mon 𝔛) public

data CMonEq : Type where
  `mon : M.MonEq -> CMonEq
  `comm : CMonEq

CMonEqFree : CMonEq -> ℕ
CMonEqFree (`mon eqn) = M.MonEqFree eqn
CMonEqFree `comm = 2

CMonEqSig : EqSig ℓ-zero ℓ-zero
CMonEqSig = finEqSig (CMonEq , CMonEqFree)

cmonEqLhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqLhs (`mon eqn) = M.monEqLhs eqn
cmonEqLhs `comm = node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ []))

cmonEqRhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqRhs (`mon eqn) = M.monEqRhs eqn
cmonEqRhs `comm = node (`⊕ , lookup (leaf fone ∷ leaf fzero ∷ []))

CMonSEq : seq CMonSig CMonEqSig
CMonSEq n = cmonEqLhs n , cmonEqRhs n

cmonSatMon : ∀ {s} {str : struct s CMonSig} -> str ⊨ CMonSEq -> str ⊨ M.MonSEq
cmonSatMon {_} {str} cmonSat eqn ρ = cmonSat (`mon eqn) ρ

module CMonSEq {ℓ} (𝔛 : CMonStruct {ℓ}) (ϕ : 𝔛 ⊨ CMonSEq) where
  open M.MonSEq (CMon→Mon 𝔛) (cmonSatMon ϕ) public

  comm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  comm m n =
      m ⊕ n
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (m ∷ n ∷ []))
    ≡⟨ cong (λ z -> 𝔛 .algebra (`⊕ , z)) (funExt lemma1) ⟩
      𝔛 .algebra (`⊕ , (λ x -> sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) x)))
    ≡⟨ ϕ `comm (lookup (m ∷ n ∷ [])) ⟩
      𝔛 .algebra (`⊕ , (λ x -> sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fone ∷ leaf fzero ∷ []) x)))
    ≡⟨ cong (λ z -> 𝔛 .algebra (`⊕ , z)) (sym (funExt lemma2)) ⟩
      𝔛 .algebra (`⊕ , lookup (n ∷ m ∷ []))
    ≡⟨⟩
      n ⊕ m ∎
    where
      lemma1 : (w : CMonSig .arity `⊕) -> lookup (m ∷ n ∷ []) w ≡ sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)
      lemma1 (zero , p) = refl
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 : (w : CMonSig .arity `⊕) -> lookup (n ∷ m ∷ []) w ≡ sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fone ∷ leaf fzero ∷ []) w)
      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

module Examples where

  ℕ-CMonStr : CMonStruct
  ℕ-CMonStr = M.Examples.ℕ-MonStr

  ℕ-CMonStr-MonSEq : ℕ-CMonStr ⊨ CMonSEq
  ℕ-CMonStr-MonSEq (`mon eqn) ρ = M.Examples.ℕ-MonStr-MonSEq eqn ρ
  ℕ-CMonStr-MonSEq `comm ρ = +-comm (ρ fzero) (ρ fone)
