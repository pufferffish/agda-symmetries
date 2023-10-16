{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Structures.Set.Mon.Desc where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma

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
  e-eta {i} = cong (\j -> 𝔛 .algebra (`e , j)) (funExt {!!})

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

  assocr : (x y z : 𝔛 .carrier) -> (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  assocr x y z =
    (x ⊕ y) ⊕ z ≡⟨ refl ⟩
    𝔛 .algebra (`⊕ , lookup (𝔛 .algebra (`⊕ , lookup (x ∷ y ∷ [])) ∷ z ∷ [])) ≡⟨ cong (\w -> 𝔛 .algebra (`⊕ , w)) (funExt {!!}) ⟩
    𝔛 .algebra (`⊕ , (\w -> sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) w))) ≡⟨ {!!} ⟩
    𝔛 .algebra (`⊕ , lookup (x ∷ 𝔛 .algebra (`⊕ , lookup (y ∷ z ∷ [])) ∷ [])) ≡⟨ refl ⟩
    x ⊕ (y ⊕ z) ∎
    -- where
    --   lemma1 : (x₁ : MonSig .arity `⊕) → lookup (𝔛 .algebra (`⊕ , lookup (x ∷ y ∷ [])) ∷ z ∷ []) x₁ ≡ sharp MonSig 𝔛 (lookup (x ∷ y ∷ z ∷ [])) (lookup (node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) x₁)
    --   lemma1 (fst₁ , snd₁) = {!!}

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
