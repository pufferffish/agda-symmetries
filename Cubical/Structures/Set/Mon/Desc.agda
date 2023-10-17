{-# OPTIONS --cubical --allow-unsolved-metas #-}

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

-- TODO: Put level variables in a public prelude
private
  variable
    ℓ : Level

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

MonStruct : ∀ {n : Level} -> Type (ℓ-suc n)
MonStruct {n} = struct n MonSig

module MonStruct (𝔛 : MonStruct {ℓ}) where
  e : 𝔛 .carrier
  e = 𝔛 .algebra (`e , lookup [])

  e-eta : {i : Arity 0 -> 𝔛 .carrier} -> 𝔛 .algebra (`e , i) ≡ e
  e-eta {i} = cong (\j -> 𝔛 .algebra (`e , j)) (funExt λ z -> lookup [] z)

  infixr 40 _⊕_
  _⊕_ : 𝔛 .carrier -> 𝔛 .carrier -> 𝔛 .carrier
  _⊕_ x y = 𝔛 .algebra (`⊕ , lookup (x ∷ y ∷ []))

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

module MonSEq (𝔛 : MonStruct {ℓ}) (ϕ : 𝔛 ⊨ MonSEq) where
  open MonStruct 𝔛 public

  unitl : ∀ m -> e ⊕ m ≡ m
  unitl m =
      e ⊕ m
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (𝔛 .algebra (`e , _) ∷ m ∷ []))
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .algebra (`⊕ , (λ x -> sharp (finSig (MonSym , MonAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , _) ∷ leaf fzero ∷ []) x)))
    ≡⟨ ϕ `unitl (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (w : MonSig .arity `⊕) -> lookup (𝔛 .algebra (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ m ∷ []) w ≡ sharp (finSig (MonSym , MonAr)) 𝔛 (lookup (m ∷ [])) (lookup (node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ leaf fzero ∷ []) w)
      lemma (zero , p) = sym e-eta
      lemma (suc zero , p) = refl
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  unitr : ∀ m -> m ⊕ e ≡ m
  unitr m =
      m ⊕ e
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (m ∷ 𝔛 .algebra (`e , _) ∷ []))  
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt lemma) ⟩
      𝔛 .algebra (`⊕ , (λ x -> sharp MonSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)))
    ≡⟨ ϕ `unitr (lookup [ m ]) ⟩
      m ∎
    where
      lemma : (x : MonSig .arity `⊕) -> lookup (m ∷ 𝔛 .algebra (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x ≡ sharp MonSig 𝔛 (lookup [ m ]) (lookup (leaf fzero ∷ node (`e , (λ num → ⊥.rec (¬Fin0 num))) ∷ []) x)
      lemma (zero , p) = refl
      lemma (suc zero , p) = sym e-eta
      lemma (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  assocr : ∀ x y z -> (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  assocr x y z =
      (x ⊕ y) ⊕ z
    ≡⟨⟩
      𝔛 .algebra (`⊕ , lookup (𝔛 .algebra (`⊕ , lookup (x ∷ y ∷ [])) ∷ z ∷ []))
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt lemma1) ⟩
      𝔛 .algebra (`⊕ , (\w -> sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)))
    ≡⟨ ϕ `assocr (lookup (x ∷ y ∷ z ∷ [])) ⟩
      𝔛 .algebra (`⊕ , (λ w -> sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)))
    ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (sym (funExt lemma3)) ⟩
      𝔛 .algebra (`⊕ , lookup (x ∷ 𝔛 .algebra (`⊕ , lookup (y ∷ z ∷ [])) ∷ []))
    ≡⟨⟩
      x ⊕ (y ⊕ z) ∎
    where
      lemma1 : (w : MonSig .arity `⊕) -> lookup (𝔛 .algebra (`⊕ , lookup (x ∷ y ∷ [])) ∷ z ∷ []) w ≡ sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w)
      lemma2 : (w : MonSig .arity `⊕) -> lookup (x ∷ y ∷ []) w ≡ sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)

      lemma1 (zero , p) = cong (λ z → 𝔛 .algebra (`⊕ , z)) (funExt lemma2)
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma3 : (w : MonSig .arity `⊕) -> lookup (x ∷ 𝔛 .algebra (`⊕ , lookup (y ∷ z ∷ [])) ∷ []) w ≡ sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (leaf fzero ∷ node (`⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) w)
      lemma4 : (w : MonSig .arity `⊕) -> lookup (y ∷ z ∷ []) w ≡ sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (leaf fone ∷ leaf ftwo ∷ []) w)

      lemma3 (zero , p) = refl
      lemma3 (suc zero , p) = cong (λ w → 𝔛 .algebra (`⊕ , w)) (funExt lemma4)
      lemma3 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma4 (zero , p) = refl
      lemma4 (suc zero , p) = refl
      lemma4 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  -- TODO: Write generic lemma about compatibility between lookup and sharp
  -- lemma : (f : MonSym) (x : 𝔛 .carrier) (xs : List (𝔛 .carrier)) (a : Arity (length xs))
  --      -> lookup (x ∷ xs) (fsuc a) ≡ sharp MonSig 𝔛 {!!} (lookup {!!} a)
  -- lemma f = {!!}

module Examples where

  ℕ-MonStr : MonStruct
  carrier ℕ-MonStr = ℕ
  algebra ℕ-MonStr (`e , _) = 0
  algebra ℕ-MonStr (`⊕ , i) = i fzero + i fone

  ℕ-MonStr-MonSEq : ℕ-MonStr ⊨ MonSEq
  ℕ-MonStr-MonSEq `unitl ρ = refl
  ℕ-MonStr-MonSEq `unitr ρ = +-zero (ρ fzero)
  ℕ-MonStr-MonSEq `assocr ρ = sym (+-assoc (ρ fzero) (ρ fone) (ρ ftwo))
