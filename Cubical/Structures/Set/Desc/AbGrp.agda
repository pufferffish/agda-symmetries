{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.Desc.AbGrp where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (-_ to -ℤ_ ; _+_ to _+ℤ_ ; _-_ to _-ℤ_) 
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Functions.Logic as L
open import Cubical.Structures.Arity as F public

open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq

import Cubical.Structures.Set.Desc.Grp as G
import Cubical.Structures.Set.Desc.Mon as M
import Cubical.Structures.Set.Desc.CMon as CM

open G.GrpSym

AbGrpSym = G.GrpSym
AbGrpAr = G.GrpAr
AbGrpFinSig = G.GrpFinSig
AbGrpSig = G.GrpSig

AbGrpStruct : ∀ {n} -> Type (ℓ-suc n)
AbGrpStruct {n} = struct n AbGrpSig

AbGrp→Grp : ∀ {ℓ} -> AbGrpStruct {ℓ} -> G.GrpStruct {ℓ}
car (AbGrp→Grp 𝔛) = 𝔛 .car
alg (AbGrp→Grp 𝔛) = 𝔛 .alg

module AbGrpStruct {ℓ} (𝔛 : AbGrpStruct {ℓ}) where
  open G.GrpStruct (AbGrp→Grp 𝔛) public

data AbGrpEq : Type where
  `grp : G.GrpEq -> AbGrpEq
  `comm : AbGrpEq

AbGrpEqFree : AbGrpEq -> ℕ
AbGrpEqFree (`grp eqn) = G.GrpEqFree eqn
AbGrpEqFree `comm = 2

AbGrpEqSig : EqSig ℓ-zero ℓ-zero
AbGrpEqSig = finEqSig (AbGrpEq , AbGrpEqFree)

abGrpEqLhs : (eq : AbGrpEq) -> FinTree AbGrpFinSig (AbGrpEqFree eq)
abGrpEqLhs (`grp eqn) = G.grpEqLhs eqn
abGrpEqLhs `comm = node (`⊕ , ⟪ leaf fzero ⨾ leaf fone ⟫)

abGrpEqRhs : (eq : AbGrpEq) -> FinTree AbGrpFinSig (AbGrpEqFree eq)
abGrpEqRhs (`grp eqn) = G.grpEqRhs eqn
abGrpEqRhs `comm = node (`⊕ , ⟪ leaf fone ⨾ leaf fzero ⟫)

AbGrpSEq : seq AbGrpSig AbGrpEqSig
AbGrpSEq n = abGrpEqLhs n , abGrpEqRhs n

abGrpSatGrp : ∀ {s} {str : struct s AbGrpSig} -> str ⊨ AbGrpSEq -> str ⊨ G.GrpSEq
abGrpSatGrp {_} {str} abGrpSat eqn ρ = abGrpSat (`grp eqn) ρ

module AbGrpSEq {ℓ} (𝔛 : AbGrpStruct {ℓ}) (ϕ : 𝔛 ⊨ AbGrpSEq) where
  open G.GrpSEq (AbGrp→Grp 𝔛) (abGrpSatGrp ϕ) public

  comm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  comm m n =
      m ⊕ n
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (m ∷ n ∷ []))
    ≡⟨ cong (λ z -> 𝔛 .alg (`⊕ , z)) (funExt lemma1) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp AbGrpSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) x)))
    ≡⟨ ϕ `comm (lookup (m ∷ n ∷ [])) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp AbGrpSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fone ∷ leaf fzero ∷ []) x)))
    ≡⟨ cong (λ z -> 𝔛 .alg (`⊕ , z)) (sym (funExt lemma2)) ⟩
      𝔛 .alg (`⊕ , lookup (n ∷ m ∷ []))
    ≡⟨⟩
      n ⊕ m ∎
    where
      lemma1 : (w : AbGrpSig .arity `⊕) -> lookup (m ∷ n ∷ []) w ≡ sharp AbGrpSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)
      lemma1 (zero , p) = refl
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 : (w : AbGrpSig .arity `⊕) -> lookup (n ∷ m ∷ []) w ≡ sharp AbGrpSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fone ∷ leaf fzero ∷ []) w)
      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  abGrpSatCMon : 𝔛 ⊨ AbGrpSEq -> G.Grp→Mon 𝔛 ⊨ CM.CMonSEq
  abGrpSatCMon abGrpSat (CM.`mon eqn) ρ = grpSatMon (abGrpSatGrp abGrpSat) eqn ρ
  abGrpSatCMon abGrpSat CM.`comm ρ =
      𝔛 .alg (`⊕ , (λ x → sharp M.MonSig (G.Grp→Mon 𝔛) ρ (⟪ leaf fzero ⨾ leaf fone ⟫ x)))
    ≡⟨ cong (λ z -> 𝔛 .alg (`⊕ , z)) (funExt lemma) ⟩
      ρ fzero ⊕ ρ fone
    ≡⟨ comm (ρ fzero) (ρ fone) ⟩
      ρ fone ⊕ ρ fzero
    ≡⟨ cong (λ z -> 𝔛 .alg (`⊕ , z)) (sym (funExt lemma)) ⟩
      𝔛 .alg (`⊕ , (λ x → sharp M.MonSig (G.Grp→Mon 𝔛) ρ (⟪ leaf fone ⨾ leaf fzero ⟫ x))) ∎
    where
      lemma : ∀ {m n} w -> sharp M.MonSig (G.Grp→Mon 𝔛) ρ (⟪ leaf m ⨾ leaf n ⟫ w) ≡ lookup (ρ m ∷ ρ n ∷ []) w
      lemma (zero , p) = refl
      lemma (suc zero , p) = refl
      lemma (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

ℤ-AbGrpStr : AbGrpStruct
ℤ-AbGrpStr = G.ℤ-GrpStr

ℤ-AbGrpStr-AbGrpSEq : ℤ-AbGrpStr ⊨ AbGrpSEq
ℤ-AbGrpStr-AbGrpSEq (`grp eqn) ρ = G.ℤ-GrpStr-GrpSEq eqn ρ
ℤ-AbGrpStr-AbGrpSEq `comm ρ = +Comm (ρ fzero) (ρ fone)
