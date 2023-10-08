{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

data FreeMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeMon A
  e : FreeMon A
  _⊕_ : FreeMon A -> FreeMon A -> FreeMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  trunc : isSet (FreeMon A)

module elimFreeMonSet {p n : Level} {A : Type n} (P : FreeMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeMon A} -> P m -> P n -> P (m ⊕ n))
                    (unitl* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*)
                    (unitr* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*)
                    (assocr* : {m n o : FreeMon A}
                               (m* : P m) ->
                               (n* : P n) ->
                               (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*)))
                    (trunc* : {xs : FreeMon A} -> isSet (P xs))
                    where
  f : (x : FreeMon A) -> P x
  f (η a) = η* a
  f e = e*
  f (x ⊕ y) = f x ⊕* f y
  f (unitl x i) = unitl* (f x) i
  f (unitr x i) = unitr* (f x) i
  f (assocr x y z i) = assocr* (f x) (f y) (f z) i
  f (trunc xs ys p q i j) =
     isOfHLevel→isOfHLevelDep 2 (\xs -> trunc* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module recFreeMonSet {p n : Level} {A : Type n} (P : Type p)
                    (η* : (a : A) -> P)
                    (e* : P)
                    (_⊕*_ : P -> P -> P)
                    (unitl* : (m* : P) -> PathP (λ i → P) (e* ⊕* m*) m*)
                    (unitr* : (m* : P) -> PathP (λ i → P) (m* ⊕* e*) m*)
                    (assocr* : (m* : P) ->
                               (n* : P) ->
                               (o* : P) -> PathP (λ i → P) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*)))
                    (trunc* : isSet P)
                    where
  f : (x : FreeMon A) -> P
  f = elimFreeMonSet.f (\_ -> P) η* e* _⊕*_ unitl* unitr* assocr* trunc*

module elimFreeMonProp {p n : Level} {A : Type n} (P : FreeMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeMon A} -> P m -> P n -> P (m ⊕ n))
                    (trunc* : {xs : FreeMon A} -> isProp (P xs))
                    where
  f : (x : FreeMon A) -> P x
  f = elimFreeMonSet.f P η* e* _⊕*_ unitl* unitr* assocr* (isProp→isSet trunc*)
    where
      abstract
        unitl* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*
        unitl* {m} m* = toPathP (trunc* (transp (λ i -> P (unitl m i)) i0 (e* ⊕* m*)) m*)
        unitr* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*
        unitr* {m} m* = toPathP (trunc* (transp (λ i -> P (unitr m i)) i0 (m* ⊕* e*)) m*)
        assocr* : {m n o : FreeMon A}
                  (m* : P m) ->
                  (n* : P n) ->
                  (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*))
        assocr* {m} {n} {o} m* n* o* =
          toPathP (trunc* (transp (λ i -> P (assocr m n o i)) i0 ((m* ⊕* n*) ⊕* o*)) (m* ⊕* (n* ⊕* o*)))

freeMon-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (FreeMon X) -> FreeMon X
freeMon-α (M.e , i) = e
freeMon-α (M.⊕ , i) = i fzero ⊕ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where
  𝔉 : struct x M.MonSig
  𝔉 = < FreeMon A , freeMon-α >

  module _ (f : A -> 𝔜 .carrier) where
    _♯ : FreeMon A -> 𝔜 .carrier
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

    _♯ (η a) = f a
    _♯ e = 𝔜 .algebra (M.e , lookup [])
    _♯ (m ⊕ n) = 𝔜 .algebra (M.⊕ , lookup (_♯ m ∷ _♯ n ∷ []))
    _♯ (unitl m i) = ♯-α m i
    _♯ (unitr m i) = ♯-β m i
    _♯ (assocr m n o i) = ♯-γ m n o i
    _♯ (trunc m n p q i j) =
      isSet𝔜 (_♯ m) (_♯ n) (cong _♯ p) (cong _♯ q) i j

    ♯-α m =
      𝔜 .algebra (M.⊕ , lookup (𝔜 .algebra (M.e , lookup []) ∷ _♯ m ∷ [])) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
      𝔜 .algebra (M.⊕ , λ z -> sharp M.MonSig 𝔜 (λ _ → _♯ m) (lookup (node (M.e , lookup []) ∷ leaf fzero ∷ []) z)) ≡⟨ 𝔜-monoid M.unitl (λ _ -> _♯ m) ⟩
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
      𝔜 .algebra (M.⊕ , λ z -> sharp M.MonSig 𝔜 (λ _ → _♯ m) (lookup (leaf fzero ∷ node (M.e , lookup []) ∷ []) z)) ≡⟨ 𝔜-monoid M.unitr (λ _ -> _♯ m) ⟩
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
      _ ≡⟨ 𝔜-monoid M.assocr (lookup (_♯ m ∷ _♯ n ∷ _♯ o ∷ [])) ⟩
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

    ♯-isMonHom : structHom 𝔉 𝔜
    ♯-isMonHom = _♯ , lemma-α
      where
      lemma-α : structIsHom 𝔉 𝔜 _♯
      lemma-β : (i : Arity 2 -> FreeMon A) (p : Arity 2) ->
        _♯ (i p)
        ≡
        lookup (_♯ (i fzero) ∷ _♯ (i fone) ∷ []) p
      lemma-α M.e i = cong (λ z -> 𝔜 .algebra (M.e , z)) (funExt λ p -> lookup [] p)
      lemma-α M.⊕ i = cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt (lemma-β i))
      lemma-β i (zero , p) = cong (_♯ ∘ i) (Σ≡Prop (λ _ -> isProp≤) refl)
      lemma-β i (suc zero , p) = cong (_♯ ∘ i) (Σ≡Prop (λ _ -> isProp≤) refl)
      lemma-β i (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

  private
    freeMonEquivLemma : (g : structHom 𝔉 𝔜) -> (x : FreeMon A) -> g .fst x ≡ ((g .fst ∘ η) ♯) x
    freeMonEquivLemma (g , homMonWit) = elimFreeMonProp.f (λ x -> g x ≡ ((g ∘ η) ♯) x)
      (λ _ -> refl)
      lemma-α
      (λ {m} {n} -> lemma-β m n)
      (isSet𝔜 _ _)
      where
      lemma-α : g e ≡ 𝔜 .algebra (M.e , (λ num → ⊥.rec (¬Fin0 num)))
      lemma-α =
        _ ≡⟨ sym (homMonWit M.e (lookup [])) ⟩
        _ ≡⟨ cong (λ p -> 𝔜 .algebra (M.e , p)) (funExt λ p -> lookup [] p) ⟩
        _ ∎
      lemma-β : (m n : FreeMon A) ->
        g m ≡ ((g ∘ η) ♯) m ->
        g n ≡ ((g ∘ η) ♯) n ->
        g (m ⊕ n)
        ≡
        𝔜 .algebra (M.⊕ , lookup (_♯ (λ x₁ → g (η x₁)) m ∷ _♯ (λ x₁ → g (η x₁)) n ∷ []))
      lemma-γ : {m n : FreeMon A} ->
        g m ≡ ((g ∘ η) ♯) m ->
        g n ≡ ((g ∘ η) ♯) n ->
       (z : Arity 2) ->
        g (lookup (m ∷ n ∷ []) z)
        ≡
        lookup (((g ∘ η) ♯) m ∷ ((g ∘ η) ♯) n ∷ []) z
      lemma-β m n p q =
        g (m ⊕ n) ≡⟨ sym (homMonWit M.⊕ (lookup (m ∷ n ∷ []))) ⟩
        _ ≡⟨ cong (λ p -> 𝔜 .algebra (M.⊕ , p)) (funExt (lemma-γ p q)) ⟩
        _ ∎
      lemma-γ p q (zero , _) = p
      lemma-γ p q (suc zero , _) = q
      lemma-γ _ _ (suc (suc fs) , p) = ⊥.rec (¬m+n<m {m = 2} p)

    freeMonEquivLemma-β : (g : structHom 𝔉 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ η)
    freeMonEquivLemma-β g = structHom≡ 𝔉 𝔜 g (♯-isMonHom (g .fst ∘ η)) isSet𝔜 (funExt (freeMonEquivLemma g))

  freeMonEquiv : structHom 𝔉 𝔜 ≃ (A -> 𝔜 .carrier)
  freeMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ η) ♯-isMonHom (λ _ -> refl) (sym ∘ freeMonEquivLemma-β))
      
module FreeMonDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

freeMon-sat : ∀ {n} {X : Type n} -> < FreeMon X , freeMon-α > ⊨ M.MonSEq
freeMon-sat M.unitl ρ = unitl (ρ fzero)
freeMon-sat M.unitr ρ = unitr (ρ fzero)
freeMon-sat M.assocr ρ = assocr (ρ fzero) (ρ fone) (ρ ftwo)

freeMonDef : FreeMonDef.Free 2
F.Definition.Free.F freeMonDef = FreeMon
F.Definition.Free.η freeMonDef = η
F.Definition.Free.α freeMonDef = freeMon-α
F.Definition.Free.sat freeMonDef = freeMon-sat
F.Definition.Free.isFree freeMonDef isSet𝔜 satMon = (Free.freeMonEquiv isSet𝔜 satMon) .snd
