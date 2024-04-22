{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.Desc.Grp where

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

import Cubical.Structures.Set.Desc.Mon as M

open M.MonSym

data GrpSym : Type where
  `e : GrpSym
  `⊕ : GrpSym
  `- : GrpSym

GrpAr : GrpSym -> ℕ
GrpAr `e = 0
GrpAr `⊕ = 2
GrpAr `- = 1

GrpFinSig : FinSig ℓ-zero
GrpFinSig = GrpSym , GrpAr

GrpSig : Sig ℓ-zero ℓ-zero
GrpSig = finSig GrpFinSig

GrpStruct : ∀ {n} -> Type (ℓ-suc n)
GrpStruct {n} = struct n GrpSig

module GrpStruct {ℓ} (𝔛 : GrpStruct {ℓ}) where
  e : 𝔛 .car
  e = 𝔛 .alg (`e , lookup [])

  e-eta : {i j : Arity 0 -> 𝔛 .car} -> 𝔛 .alg (`e , i) ≡ 𝔛 .alg (`e , j)
  e-eta {i} = cong (\j -> 𝔛 .alg (`e , j)) (funExt λ z -> lookup [] z)

  infixr 40 _⊕_
  _⊕_ : 𝔛 .car -> 𝔛 .car -> 𝔛 .car
  _⊕_ x y = 𝔛 .alg (`⊕ , lookup (x ∷ y ∷ []))

  ⊕-eta : ∀ {ℓ} {A : Type ℓ} (i : Arity 2 -> A) (_♯ : A -> 𝔛 .car) -> 𝔛 .alg (`⊕ , (λ w -> i w ♯)) ≡ (i fzero ♯) ⊕ (i fone ♯)
  ⊕-eta i _♯ = cong (λ z -> 𝔛 .alg (`⊕ , z)) (funExt lemma)
    where
    lemma : (x : Arity 2) -> (i x ♯) ≡ lookup ((i fzero ♯) ∷ (i fone ♯) ∷ []) x
    lemma (zero , p) = cong (_♯ ∘ i) (Σ≡Prop (λ _ -> isProp≤) refl)
    lemma (suc zero , p) = cong (_♯ ∘ i) (Σ≡Prop (λ _ -> isProp≤) refl)
    lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  infix 45 -_
  -_ : 𝔛 .car -> 𝔛 .car
  -_ x = 𝔛 .alg (`- , lookup [ x ])

data GrpEq : Type where
  `unitl `unitr `assocr `invl `invr : GrpEq

GrpEqFree : GrpEq -> ℕ
GrpEqFree `unitl = 1
GrpEqFree `unitr = 1
GrpEqFree `assocr = 3
GrpEqFree `invl = 1
GrpEqFree `invr = 1

GrpEqSig : EqSig ℓ-zero ℓ-zero
GrpEqSig = finEqSig (GrpEq , GrpEqFree)

grpEqLhs : (eq : GrpEq) -> FinTree GrpFinSig (GrpEqFree eq)
grpEqLhs `unitl = node (`⊕ , ⟪ node (`e , ⟪⟫) ⨾ leaf fzero ⟫)
grpEqLhs `unitr = node (`⊕ , ⟪ leaf fzero ⨾ node (`e , ⟪⟫) ⟫)
grpEqLhs `assocr = node (`⊕ , ⟪ node (`⊕ , ⟪ leaf fzero ⨾ leaf fone ⟫) ⨾ leaf ftwo ⟫)
grpEqLhs `invl  = node (`⊕ , ⟪ node (`- , ⟪ leaf fzero ⟫) ⨾ leaf fzero ⟫)
grpEqLhs `invr  = node (`⊕ , ⟪ leaf fzero ⨾ node (`- , ⟪ leaf fzero ⟫)⟫)

grpEqRhs : (eq : GrpEq) -> FinTree GrpFinSig (GrpEqFree eq)
grpEqRhs `unitl = leaf fzero
grpEqRhs `unitr = leaf fzero
grpEqRhs `assocr = node (`⊕ , ⟪ leaf fzero ⨾ node (`⊕ , ⟪ leaf fone ⨾ leaf ftwo ⟫)⟫)
grpEqRhs `invl  = node (`e , ⟪⟫)
grpEqRhs `invr  = node (`e , ⟪⟫)

GrpSEq : seq GrpSig GrpEqSig
GrpSEq n = grpEqLhs n , grpEqRhs n

Grp→Mon : ∀ {ℓ} -> GrpStruct {ℓ} -> M.MonStruct {ℓ}
car (Grp→Mon 𝔛) = 𝔛 .car
alg (Grp→Mon 𝔛) (`e , i) = alg 𝔛 (`e , i)
alg (Grp→Mon 𝔛) (`⊕ , i) = alg 𝔛 (`⊕ , i)

module GrpSEq {ℓ} (𝔛 : GrpStruct {ℓ}) (ϕ : 𝔛 ⊨ GrpSEq) where
  open GrpStruct 𝔛 public

  unitl : ∀ m -> e ⊕ m ≡ m
  unitl m =
      e ⊕ m
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (𝔛 .alg (`e , _) ∷ m ∷ []))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp (finSig (GrpSym , GrpAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , _) ∷ leaf fzero ∷ []) x)))
    ≡⟨ ϕ `unitl (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (w : GrpSig .arity `⊕) -> lookup (𝔛 .alg (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ m ∷ []) w ≡ sharp (finSig (GrpSym , GrpAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ leaf fzero ∷ []) w)
      lemma (zero , p) = sym e-eta
      lemma (suc zero , p) = refl
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  unitr : ∀ m -> m ⊕ e ≡ m
  unitr m =
      m ⊕ e
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (m ∷ 𝔛 .alg (`e , _) ∷ []))  
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp GrpSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)))
    ≡⟨ ϕ `unitr (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (x : GrpSig .arity `⊕) -> lookup (m ∷ 𝔛 .alg (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x ≡ sharp GrpSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)
      lemma (zero , p) = refl
      lemma (suc zero , p) = sym e-eta
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  assocr m n o =
      (m ⊕ n) ⊕ o
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (𝔛 .alg (`⊕ , lookup (m ∷ n ∷ [])) ∷ o ∷ []))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma1) ⟩
      𝔛 .alg (`⊕ , (\w -> sharp GrpSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)))
    ≡⟨ ϕ `assocr (lookup (m ∷ n ∷ o ∷ [])) ⟩
      𝔛 .alg (`⊕ , (λ w -> sharp GrpSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (sym (funExt lemma3)) ⟩
      𝔛 .alg (`⊕ , lookup (m ∷ 𝔛 .alg (`⊕ , lookup (n ∷ o ∷ [])) ∷ []))
    ≡⟨⟩
      m ⊕ (n ⊕ o) ∎
    where
      lemma1 : (w : GrpSig .arity `⊕) -> lookup (𝔛 .alg (`⊕ , lookup (m ∷ n ∷ [])) ∷ o ∷ []) w ≡ sharp GrpSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)
      lemma2 : (w : GrpSig .arity `⊕) -> lookup (m ∷ n ∷ []) w ≡ sharp GrpSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)

      lemma1 (zero , p) = cong (λ o → 𝔛 .alg (`⊕ , o)) (funExt lemma2)
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma3 : (w : GrpSig .arity `⊕) -> lookup (m ∷ 𝔛 .alg (`⊕ , lookup (n ∷ o ∷ [])) ∷ []) w ≡ sharp GrpSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)
      lemma4 : (w : GrpSig .arity `⊕) -> lookup (n ∷ o ∷ []) w ≡ sharp GrpSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fone ∷ leaf ftwo ∷ []) w)

      lemma3 (zero , p) = refl
      lemma3 (suc zero , p) = cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma4)
      lemma3 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma4 (zero , p) = refl
      lemma4 (suc zero , p) = refl
      lemma4 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  private
    fin1Reduce : {ℓA : Level} {A : Type ℓA} {f g : Arity 1 -> A}
      -> f fzero ≡ g fzero
      -> f ≡ g
    fin1Reduce {f = f} {g = g} p = funExt $ λ k ->
      f k ≡⟨ cong f (isContr→isProp isContrFin1 k fzero) ⟩
      f fzero ≡⟨ p ⟩
      g fzero ≡⟨ cong g (isContr→isProp isContrFin1 fzero k) ⟩
      g k ∎

  invl : ∀ m -> - m ⊕ m ≡ e
  invl m =
      𝔛 .alg (`⊕ , lookup (𝔛 .alg (`- , lookup (m ∷ [])) ∷ m ∷ []))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma1) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp GrpSig 𝔛 (lookup [ m ]) (⟪ node (`- , ⟪ leaf fzero ⟫) ⨾ leaf fzero ⟫ x)))
    ≡⟨ ϕ `invl (lookup [ m ]) ⟩
      𝔛 .alg (`e , (λ x → sharp GrpSig 𝔛 (lookup [ m ]) (⟪⟫ x)))
    ≡⟨ e-eta ⟩
      e ∎
    where
      lemma1 : (x : GrpSig .arity `⊕) -> lookup (𝔛 .alg (`- , lookup (m ∷ [])) ∷ m ∷ []) x ≡ sharp GrpSig 𝔛 (lookup [ m ]) (⟪ node (`- , ⟪ leaf fzero ⟫) ⨾ leaf fzero ⟫ x)
      lemma1 (zero , p) = cong (λ w → 𝔛 .alg (`- , w)) (fin1Reduce refl)
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  invr : ∀ m -> m ⊕ - m ≡ e
  invr m =
      𝔛 .alg (`⊕ , lookup (m ∷ 𝔛 .alg (`- , lookup (m ∷ [])) ∷ []))
    ≡⟨ cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma1) ⟩
      𝔛 .alg (`⊕ , (λ x → sharp GrpSig 𝔛 (lookup [ m ]) (⟪ leaf fzero ⨾ node (`- , ⟪ leaf fzero ⟫) ⟫ x)))
    ≡⟨ ϕ `invr (lookup [ m ]) ⟩
      𝔛 .alg (`e , (λ x → sharp GrpSig 𝔛 (lookup [ m ]) (⟪⟫ x)))
    ≡⟨ e-eta ⟩
      e ∎
    where
      lemma1 : (x : GrpSig .arity `⊕) -> lookup (m ∷ 𝔛 .alg (`- , lookup (m ∷ [])) ∷ []) x ≡ sharp GrpSig 𝔛 (lookup [ m ]) (⟪ leaf fzero ⨾ node (`- , ⟪ leaf fzero ⟫) ⟫ x)
      lemma1 (zero , p) = refl
      lemma1 (suc zero , p) = cong (λ w → 𝔛 .alg (`- , w)) (fin1Reduce refl)
      lemma1 (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  grpSatMon : 𝔛 ⊨ GrpSEq -> Grp→Mon 𝔛 ⊨ M.MonSEq
  grpSatMon grpSat M.`unitl ρ =
      𝔛 .alg (`⊕ , (λ x → sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ node (M.`e , ⟪⟫) ⨾ leaf fzero ⟫ x)))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .alg (`⊕ , ⟪ 𝔛 .alg (`e , ⟪⟫) ⨾ ρ fzero ⟫)
    ≡⟨ unitl (ρ fzero) ⟩
      ρ fzero ∎
    where
      lemma : (w : GrpSig .arity `⊕) -> sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ node (`e , ⟪⟫) ⨾ leaf fzero ⟫ w) ≡ ⟪ 𝔛 .alg (`e , ⟪⟫) ⨾ ρ fzero ⟫ w
      lemma (zero , p) = e-eta
      lemma (suc zero , p) = refl
      lemma (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)
  grpSatMon grpSat M.`unitr ρ =
      𝔛 .alg (`⊕ , (λ x → sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ leaf fzero ⨾ node (`e , ⟪⟫) ⟫ x)))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .alg (`⊕ , ⟪ ρ fzero ⨾ 𝔛 .alg (`e , ⟪⟫) ⟫)
    ≡⟨ unitr (ρ fzero) ⟩
      ρ fzero ∎
    where
      lemma : (w : GrpSig .arity `⊕) -> sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ leaf fzero ⨾ node (`e , ⟪⟫) ⟫ w) ≡ ⟪ ρ fzero ⨾ 𝔛 .alg (`e , ⟪⟫) ⟫ w
      lemma (zero , p) = refl
      lemma (suc zero , p) = e-eta
      lemma (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)
  grpSatMon grpSat M.`assocr ρ =
      𝔛 .alg (`⊕ , (λ x → sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ node (`⊕ , ⟪ leaf fzero ⨾ leaf fone ⟫) ⨾ leaf ftwo ⟫ x)))
    ≡⟨ cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma1) ⟩
      (ρ fzero ⊕ ρ fone) ⊕ ρ ftwo
    ≡⟨ assocr (ρ fzero) (ρ fone) (ρ ftwo) ⟩
      ρ fzero ⊕ (ρ fone ⊕ ρ ftwo)
    ≡⟨ cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma3) ⟩
      𝔛 .alg (`⊕ , (λ x → sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ leaf fzero ⨾ node (`⊕ , ⟪ leaf fone ⨾ leaf ftwo ⟫) ⟫ x))) ∎
    where
      lemma1 : (w : GrpSig .arity `⊕) -> sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ node (`⊕ , ⟪ leaf fzero ⨾ leaf fone ⟫) ⨾ leaf ftwo ⟫ w) ≡ lookup (ρ fzero ⊕ ρ fone ∷ ρ ftwo ∷ []) w
      lemma2 : (w : GrpSig .arity `⊕) -> sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ leaf fzero ⨾ leaf fone ⟫ w) ≡ lookup (ρ fzero ∷ ρ fone ∷ []) w

      lemma1 (zero , p) = cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma2)
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 (zero , p) = refl 
      lemma2 (suc zero , p) = refl 
      lemma2 (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma3 : (w : GrpSig .arity `⊕) -> lookup (ρ fzero ∷ ρ fone ⊕ ρ ftwo ∷ []) w ≡ sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ leaf fzero ⨾ node (`⊕ , ⟪ leaf fone ⨾ leaf ftwo ⟫) ⟫ w)
      lemma4 : (w : GrpSig .arity `⊕) -> lookup (ρ fone ∷ ρ ftwo ∷ []) w ≡ sharp M.MonSig (Grp→Mon 𝔛) ρ (⟪ leaf fone ⨾ leaf ftwo ⟫ w)

      lemma3 (zero , p) = refl 
      lemma3 (suc zero , p) = cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma4) 
      lemma3 (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma4 (zero , p) = refl 
      lemma4 (suc zero , p) = refl 
      lemma4 (suc (suc k) , p) = ⊥.rec (¬m+n<m {m = 2} p)

ℤ-GrpStr : GrpStruct
car ℤ-GrpStr = ℤ 
alg ℤ-GrpStr (`e , i) = pos 0 
alg ℤ-GrpStr (`⊕ , i) = i fzero +ℤ i fone
alg ℤ-GrpStr (`- , i) = -ℤ (i fzero)

ℤ-GrpStr-GrpSEq : ℤ-GrpStr ⊨ GrpSEq
ℤ-GrpStr-GrpSEq `unitl ρ = sym (pos0+ (ρ fzero))
ℤ-GrpStr-GrpSEq `unitr ρ = +Comm (ρ fzero) 0 ∙ sym (pos0+ (ρ fzero))
ℤ-GrpStr-GrpSEq `assocr ρ = sym (+Assoc (ρ fzero) (ρ fone) (ρ ftwo))
ℤ-GrpStr-GrpSEq `invl ρ = -Cancel' (ρ fzero)
ℤ-GrpStr-GrpSEq `invr ρ = +Comm (ρ fzero) (-ℤ (ρ fzero)) ∙ -Cancel' (ρ fzero)
