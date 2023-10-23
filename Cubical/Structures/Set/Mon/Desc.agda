{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree as T
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity as F

data MonSym : Type where
  `e : MonSym
  `⊕ : MonSym

MonAr : MonSym -> ℕ
MonAr `e = 0
MonAr `⊕ = 2

MonFinSig : FinSig ℓ-zero
MonFinSig = MonSym , MonAr

MonSig : Sig ℓ-zero ℓ-zero
MonSig = finSig MonFinSig

MonStruct : ∀ {n} -> Type (ℓ-suc n)
MonStruct {n} = struct n MonSig

module MonStruct {ℓ} (𝔛 : MonStruct {ℓ}) where
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

data MonEq : Type where
  `unitl `unitr `assocr : MonEq

MonEqFree : MonEq -> ℕ
MonEqFree `unitl = 1
MonEqFree `unitr = 1
MonEqFree `assocr = 3

MonEqSig : EqSig ℓ-zero ℓ-zero
MonEqSig = finEqSig (MonEq , MonEqFree)

monEqLhs : (eq : MonEq) -> FinTree MonFinSig (MonEqFree eq)
monEqLhs `unitl = node (`⊕ , lookup (node (`e , lookup []) ∷ leaf fzero ∷ []))
monEqLhs `unitr = node (`⊕ , lookup (leaf fzero ∷ node (`e , lookup []) ∷ []))
monEqLhs `assocr = node (`⊕ , lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []))

monEqRhs : (eq : MonEq) -> FinTree MonFinSig (MonEqFree eq)
monEqRhs `unitl = leaf fzero
monEqRhs `unitr = leaf fzero
monEqRhs `assocr = node (`⊕ , lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []))

MonSEq : seq MonSig MonEqSig
MonSEq n = monEqLhs n , monEqRhs n

module MonSEq {ℓ} (𝔛 : MonStruct {ℓ}) (ϕ : 𝔛 ⊨ MonSEq) where
  open MonStruct 𝔛 public

  unitl : ∀ m -> e ⊕ m ≡ m
  unitl m =
      e ⊕ m
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (𝔛 .alg (`e , _) ∷ m ∷ []))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp (finSig (MonSym , MonAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , _) ∷ leaf fzero ∷ []) x)))
    ≡⟨ ϕ `unitl (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (w : MonSig .arity `⊕) -> lookup (𝔛 .alg (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ m ∷ []) w ≡ sharp (finSig (MonSym , MonAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ leaf fzero ∷ []) w)
      lemma (zero , p) = sym e-eta
      lemma (suc zero , p) = refl
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  unitr : ∀ m -> m ⊕ e ≡ m
  unitr m =
      m ⊕ e
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (m ∷ 𝔛 .alg (`e , _) ∷ []))  
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp MonSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)))
    ≡⟨ ϕ `unitr (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (x : MonSig .arity `⊕) -> lookup (m ∷ 𝔛 .alg (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x ≡ sharp MonSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)
      lemma (zero , p) = refl
      lemma (suc zero , p) = sym e-eta
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  assocr m n o =
      (m ⊕ n) ⊕ o
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (𝔛 .alg (`⊕ , lookup (m ∷ n ∷ [])) ∷ o ∷ []))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (funExt lemma1) ⟩
      𝔛 .alg (`⊕ , (\w -> sharp MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)))
    ≡⟨ ϕ `assocr (lookup (m ∷ n ∷ o ∷ [])) ⟩
      𝔛 .alg (`⊕ , (λ w -> sharp MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)))
    ≡⟨ cong (\w -> 𝔛 .alg (`⊕ , w)) (sym (funExt lemma3)) ⟩
      𝔛 .alg (`⊕ , lookup (m ∷ 𝔛 .alg (`⊕ , lookup (n ∷ o ∷ [])) ∷ []))
    ≡⟨⟩
      m ⊕ (n ⊕ o) ∎
    where
      lemma1 : (w : MonSig .arity `⊕) -> lookup (𝔛 .alg (`⊕ , lookup (m ∷ n ∷ [])) ∷ o ∷ []) w ≡ sharp MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)
      lemma2 : (w : MonSig .arity `⊕) -> lookup (m ∷ n ∷ []) w ≡ sharp MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)

      lemma1 (zero , p) = cong (λ o → 𝔛 .alg (`⊕ , o)) (funExt lemma2)
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma3 : (w : MonSig .arity `⊕) -> lookup (m ∷ 𝔛 .alg (`⊕ , lookup (n ∷ o ∷ [])) ∷ []) w ≡ sharp MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)
      lemma4 : (w : MonSig .arity `⊕) -> lookup (n ∷ o ∷ []) w ≡ sharp MonSig 𝔛 (lookup (m ∷ n ∷ o ∷ [])) (lookup (leaf fone ∷ leaf ftwo ∷ []) w)

      lemma3 (zero , p) = refl
      lemma3 (suc zero , p) = cong (λ w → 𝔛 .alg (`⊕ , w)) (funExt lemma4)
      lemma3 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma4 (zero , p) = refl
      lemma4 (suc zero , p) = refl
      lemma4 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  -- TODO: Write generic lemma about compatibility between lookup and sharp
  -- lemma : (f : MonSym) (x : 𝔛 .car) (xs : List (𝔛 .car)) (a : Arity (length xs))
  --      -> lookup (x ∷ xs) (fsuc a) ≡ sharp MonSig 𝔛 {!!} (lookup {!!} a)
  -- lemma f = {!!}

ℕ-MonStr : MonStruct
car ℕ-MonStr = ℕ
alg ℕ-MonStr (`e , _) = 0
alg ℕ-MonStr (`⊕ , i) = i fzero + i fone

ℕ-MonStr-MonSEq : ℕ-MonStr ⊨ MonSEq
ℕ-MonStr-MonSEq `unitl ρ = refl
ℕ-MonStr-MonSEq `unitr ρ = +-zero (ρ fzero)
ℕ-MonStr-MonSEq `assocr ρ = sym (+-assoc (ρ fzero) (ρ fone) (ρ ftwo))
