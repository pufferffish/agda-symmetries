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

module CMonStruct {ℓ} (𝔛 : CMonStruct {ℓ}) where
  e : 𝔛 .carrier
  e = 𝔛 .algebra (`e , lookup [])

  e-eta : {i j : Arity 0 -> 𝔛 .carrier} -> 𝔛 .algebra (`e , i) ≡ 𝔛 .algebra (`e , j)
  e-eta {i} = cong (\j -> 𝔛 .algebra (`e , j)) (funExt λ z -> lookup [] z)

  infixr 40 _⊕_
  _⊕_ : 𝔛 .carrier -> 𝔛 .carrier -> 𝔛 .carrier
  _⊕_ x y = 𝔛 .algebra (`⊕ , lookup (x ∷ y ∷ []))

  ⊕-eta : ∀ {ℓ} {A : Type ℓ} (i : Arity 2 -> A) (_♯ : A -> 𝔛 .carrier) -> 𝔛 .algebra (`⊕ , (λ w -> i w ♯)) ≡ (i fzero ♯) ⊕ (i fone ♯)
  ⊕-eta i _♯ = cong (λ z -> 𝔛 .algebra (`⊕ , z)) (funExt lemma)
    where
    lemma : (x : Arity 2) -> (i x ♯) ≡ lookup ((i fzero ♯) ∷ (i fone ♯) ∷ []) x
    lemma (zero , p) = cong (_♯ ∘ i) (Σ≡Prop (λ _ -> isProp≤) refl)
    lemma (suc zero , p) = cong (_♯ ∘ i) (Σ≡Prop (λ _ -> isProp≤) refl)
    lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

data CMonEq : Type where
  `unitl `unitr `assocr `comm : CMonEq

CMonEqFree : CMonEq -> ℕ
CMonEqFree `unitl = 1
CMonEqFree `unitr = 1
CMonEqFree `assocr = 3
CMonEqFree `comm = 2

CMonEqSig : EqSig ℓ-zero ℓ-zero
CMonEqSig = finEqSig (CMonEq , CMonEqFree)

cmonEqLhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqLhs `unitl = node (`⊕ , lookup (node (`e , lookup []) ∷ leaf fzero ∷ []))
cmonEqLhs `unitr = node (`⊕ , lookup (leaf fzero ∷ node (`e , lookup []) ∷ []))
cmonEqLhs `assocr = node (`⊕ , lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []))
cmonEqLhs `comm = node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ []))

cmonEqRhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqRhs `unitl = leaf fzero
cmonEqRhs `unitr = leaf fzero
cmonEqRhs `assocr = node (`⊕ , lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []))
cmonEqRhs `comm = node (`⊕ , lookup (leaf fone ∷ leaf fzero ∷ []))

CMonSEq : seq CMonSig CMonEqSig
CMonSEq n = cmonEqLhs n , cmonEqRhs n

module CMonSEq {ℓ} (𝔛 : CMonStruct {ℓ}) (ϕ : 𝔛 ⊨ CMonSEq) where
  open CMonStruct 𝔛 public

  unitl : ∀ m -> e ⊕ m ≡ m
  unitl m =
      e ⊕ m
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (𝔛 .algebra (`e , _) ∷ m ∷ []))
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .algebra (`⊕ , (λ x -> sharp (finSig (M.MonSym , M.MonAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , _) ∷ leaf fzero ∷ []) x)))
    ≡⟨ ϕ `unitl (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (w : CMonSig .arity `⊕) -> lookup (𝔛 .algebra (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ m ∷ []) w ≡ sharp (finSig (M.MonSym , M.MonAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ leaf fzero ∷ []) w)
      lemma (zero , p) = sym e-eta
      lemma (suc zero , p) = refl
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  unitr : ∀ m -> m ⊕ e ≡ m
  unitr m =
      m ⊕ e
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (m ∷ 𝔛 .algebra (`e , _) ∷ []))  
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .algebra (`⊕ , (λ x -> sharp M.MonSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)))
    ≡⟨ ϕ `unitr (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (x : M.MonSig .arity `⊕) -> lookup (m ∷ 𝔛 .algebra (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x ≡ sharp M.MonSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)
      lemma (zero , p) = refl
      lemma (suc zero , p) = sym e-eta
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  assocr m n o =
      (m ⊕ n) ⊕ o
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (𝔛 .algebra (`⊕ , lookup (m ∷ n ∷ [])) ∷ o ∷ []))
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt lemma1) ⟩
      𝔛 .algebra (`⊕ , (\w -> sharp M.MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)))
    ≡⟨ ϕ `assocr (lookup (m ∷ n ∷ o ∷ [])) ⟩
      𝔛 .algebra (`⊕ , (λ w -> sharp M.MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)))
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (sym (funExt lemma3)) ⟩
      𝔛 .algebra (`⊕ , lookup (m ∷ 𝔛 .algebra (`⊕ , lookup (n ∷ o ∷ [])) ∷ []))
    ≡⟨⟩
      m ⊕ (n ⊕ o) ∎
    where
      lemma1 : (w : M.MonSig .arity `⊕) -> lookup (𝔛 .algebra (`⊕ , lookup (m ∷ n ∷ [])) ∷ o ∷ []) w ≡ sharp M.MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)
      lemma2 : (w : M.MonSig .arity `⊕) -> lookup (m ∷ n ∷ []) w ≡ sharp M.MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)

      lemma1 (zero , p) = cong (λ o → 𝔛 .algebra (`⊕ , o)) (funExt lemma2)
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma3 : (w : M.MonSig .arity `⊕) -> lookup (m ∷ 𝔛 .algebra (`⊕ , lookup (n ∷ o ∷ [])) ∷ []) w ≡ sharp M.MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)
      lemma4 : (w : M.MonSig .arity `⊕) -> lookup (n ∷ o ∷ []) w ≡ sharp M.MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fone ∷ leaf ftwo ∷ []) w)

      lemma3 (zero , p) = refl
      lemma3 (suc zero , p) = cong (λ w → 𝔛 .algebra (`⊕ , w)) (funExt lemma4)
      lemma3 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma4 (zero , p) = refl
      lemma4 (suc zero , p) = refl
      lemma4 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

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

cmonSatMon : ∀ {s} {str : struct s CMonSig} -> str ⊨ CMonSEq -> str ⊨ M.MonSEq
cmonSatMon {_} {str} cmonSat M.`unitl ρ = cmonSat `unitl ρ
cmonSatMon {_} {str} cmonSat M.`unitr ρ = cmonSat `unitr ρ
cmonSatMon {_} {str} cmonSat M.`assocr ρ = cmonSat `assocr ρ

module Examples where

  ℕ-CMonStr : CMonStruct
  ℕ-CMonStr = M.Examples.ℕ-MonStr

  ℕ-CMonStr-MonSEq : ℕ-CMonStr ⊨ CMonSEq
  ℕ-CMonStr-MonSEq `unitl ρ = refl
  ℕ-CMonStr-MonSEq `unitr ρ = +-zero (ρ fzero)
  ℕ-CMonStr-MonSEq `assocr ρ = sym (+-assoc (ρ fzero) (ρ fone) (ρ ftwo))
  ℕ-CMonStr-MonSEq `comm ρ = +-comm (ρ fzero) (ρ fone)
