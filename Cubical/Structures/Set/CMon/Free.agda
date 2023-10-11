{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.Free as FM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

data FreeCMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeCMon A
  e : FreeCMon A
  _⊕_ : FreeCMon A -> FreeCMon A -> FreeCMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  comm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  trunc : isSet (FreeCMon A)

private
  variable
    ℓ : Level
    A X : Type ℓ

freeCMon-α : sig M.MonSig (FreeCMon X) -> FreeCMon X
freeCMon-α (M.e , _) = e
freeCMon-α (M.⊕ , i) = i fzero ⊕ i fone

𝔉 : (A : Type ℓ) -> struct ℓ M.MonSig
𝔉 A = < FreeCMon A , freeCMon-α >

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where

  module _ (f : A -> 𝔜 .carrier) where
    _♯ : FreeCMon A -> 𝔜 .carrier
    ♯-α :
      ∀ m ->
      𝔜 .algebra (M.⊕ , lookup (𝔜 .algebra (M.e , lookup []) ∷ _♯ m ∷ []))
      ≡
      _♯ m
    ♯-β :
      ∀ m ->
      𝔜 .algebra (M.⊕ , lookup (_♯ m ∷ 𝔜 .algebra (M.e , lookup []) ∷ []))
      ≡
      _♯ m
    ♯-γ :
      ∀ m n o ->
      𝔜 .algebra (M.⊕ , lookup (𝔜 .algebra (M.⊕ , lookup (_♯ m ∷ _♯ n ∷ [])) ∷ _♯ o ∷ []))
      ≡
      𝔜 .algebra (M.⊕ , lookup (_♯ m ∷ 𝔜 .algebra (M.⊕ , lookup (_♯ n ∷ _♯ o ∷ [])) ∷ []))

    η a ♯ = f a
    e ♯ = 𝔜 .algebra (M.e , lookup [])
    (m ⊕ n) ♯ = 𝔜 .algebra (M.⊕ , lookup (m ♯ ∷ n ♯ ∷ []))
    unitl m i ♯ = FM.Free.♯-α isSet𝔜 {! 𝔜-cmon   !} f {! m  !} i -- somehow transport proofs from FreeMon to FreeCMon?
    unitr m i ♯ = ♯-β m i
    assocr m n o i ♯ = ♯-γ m n o i
    comm m n i ♯ = {! !}
    (trunc m n p q i j) ♯ =
      isSet𝔜 (_♯ m) (_♯ n) (cong _♯ p) (cong _♯ q) i j

    ♯-α m =
      𝔜 .algebra (M.⊕ , lookup (𝔜 .algebra (M.e , lookup []) ∷ _♯ m ∷ [])) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
      𝔜 .algebra (M.⊕ , λ z -> sharp M.MonSig 𝔜 (λ _ → _♯ m) (lookup (node (M.e , lookup []) ∷ leaf fzero ∷ []) z)) ≡⟨ 𝔜-cmon M.unitl (λ _ -> _♯ m) ⟩
      _♯ m ∎
      where
      lemma : (z : Arity 2) ->
        lookup (𝔜 .algebra (M.e , lookup []) ∷ _♯ m ∷ []) z
        ≡
        sharp M.MonSig 𝔜 (λ _ → _♯ m) (lookup (node (M.e , lookup []) ∷ leaf fzero ∷ []) z)
      lemma (zero , p) = cong (λ q → 𝔜 .algebra (M.e , q)) (funExt λ z -> lookup [] z)
      lemma (suc zero , p) = refl
      lemma (suc (suc _), p) = ⊥.rec (¬m+n<m {m = 2} p)
    ♯-β m =
      𝔜 .algebra (M.⊕ , lookup (_♯ m ∷ 𝔜 .algebra (M.e , lookup []) ∷ [])) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
      𝔜 .algebra (M.⊕ , λ z -> sharp M.MonSig 𝔜 (λ _ → _♯ m) (lookup (leaf fzero ∷ node (M.e , lookup []) ∷ []) z)) ≡⟨ 𝔜-cmon M.unitr (λ _ -> _♯ m) ⟩
      _♯ m ∎
      where
      lemma : (z : Arity 2) ->
        lookup (_♯ m ∷ 𝔜 .algebra (M.e , lookup []) ∷ []) z
        ≡
        sharp M.MonSig 𝔜 (λ _ → _♯ m) (lookup (leaf fzero ∷ node (M.e , lookup []) ∷ []) z)
      lemma (zero , p) = refl
      lemma (suc zero , p) = cong (λ q → 𝔜 .algebra (M.e , q)) (funExt λ z -> lookup [] z)
      lemma (suc (suc _), p) = ⊥.rec (¬m+n<m {m = 2} p)
    ♯-γ m n o =
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-α) ⟩
      _ ≡⟨ 𝔜-cmon M.assocr (lookup (_♯ m ∷ _♯ n ∷ _♯ o ∷ [])) ⟩
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-γ) ⟩
      _ ∎
      where
      lemma-α : (z : Arity 2) ->
        lookup (𝔜 .algebra (M.⊕ , lookup (_♯ m ∷ _♯ n ∷ [])) ∷ _♯ o ∷ []) z
        ≡
        sharp M.MonSig 𝔜 (lookup (_♯ m ∷ _♯ n ∷ _♯ o ∷ [])) (lookup (node (M.⊕ , lookup (leaf fzero ∷ leaf fone ∷ [])) ∷ leaf ftwo ∷ []) z)
      lemma-β : (z : Arity 2) ->
        lookup (_♯ m ∷ _♯ n ∷ []) z
        ≡
        sharp M.MonSig 𝔜 (lookup (_♯ m ∷ _♯ n ∷ _♯ o ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) z)
      lemma-α (zero , p) = cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-β)
      lemma-α (suc zero , p) = refl
      lemma-α (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)
      lemma-β (zero , p) = refl
      lemma-β (suc zero , p) = refl
      lemma-β (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)
      lemma-γ : (z : Arity 2) ->
        sharp M.MonSig 𝔜 (lookup (_♯ m ∷ _♯ n ∷ [ _♯ o ])) (lookup (leaf fzero ∷ node (M.⊕ , lookup (leaf fone ∷ leaf ftwo ∷ [])) ∷ []) z)
        ≡
        lookup (_♯ m ∷ 𝔜 .algebra (M.⊕ , lookup (_♯ n ∷ _♯ o ∷ [])) ∷ []) z
      lemma-δ : (z : Arity 2) ->
        sharp M.MonSig 𝔜 (lookup (_♯ m ∷ _♯ n ∷ [ _♯ o ])) (lookup (leaf fone ∷ leaf ftwo ∷ []) z)
        ≡
        lookup (_♯ n ∷ _♯ o ∷ []) z
      lemma-γ (zero , p) = refl
      lemma-γ (suc zero , p) = cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-δ)
      lemma-γ (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)
      lemma-δ (zero , p) = refl
      lemma-δ (suc zero , p) = refl
      lemma-δ (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

