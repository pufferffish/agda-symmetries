{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List as L
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Set.Mon.Array
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A : Type ℓ

SymmAction : ∀ {A : Type ℓ} -> Array A -> Array A -> Type ℓ
SymmAction (n , v) (m , w) = Σ[ σ ∈ Fin n ≃ Fin m ] v ≡ w ∘ σ .fst

symmActionLength≡ : ∀ {A : Type ℓ} {n m : ℕ} {v : Fin n -> A} {w : Fin m -> A} ->
  SymmAction (n , v) (m , w) -> n ≡ m
symmActionLength≡ {n = n} {m = m} (act , eqn) with discreteℕ n m
... | yes p = p
... | no ¬p = ⊥.rec (¬p (Fin-inj n m (ua act)))

equivFun∘invEq : ∀ {n m} (act : Fin n ≃ Fin m) w -> (equivFun act ∘ invEq act) w ≡ w
equivFun∘invEq act w = invEq≡→equivFun≡ act refl

invEq∘equivFun : ∀ {n m} (act : Fin n ≃ Fin m) w -> (invEq act ∘ equivFun act) w ≡ w
invEq∘equivFun act w = equivFun∘invEq (invEquiv act) w

symm-append : ∀ {xs ys} -> SymmAction xs ys -> {zs : Array A} -> SymmAction (xs ⊕ zs) (ys ⊕ zs)
symm-append {xs = (n , xs)} {ys = (m , ys)} (act , eqn) {zs = (o , zs)} =
  isoToEquiv (iso to from to∘from from∘to) , {!   !}
  where
  to : Fin (n + o) -> Fin (m + o) 
  to = combine n o (finCombine m o ∘ inl ∘ equivFun act) (finCombine m o ∘ inr)

  from : Fin (m + o) -> Fin (n + o)
  from = combine m o (finCombine n o ∘ inl ∘ invEq act) (finCombine n o ∘ inr)

  to∘from : ∀ x -> to (from x) ≡ x
  to∘from (w , p) with w ≤? m
  to∘from (w , p) | inl q with fst (invEq act (w , q)) ≤? n
  to∘from (w , p) | inl q | inl r =
    ΣPathP (lemma , toPathP (isProp≤ _ p))
    where
    lemma : _
    lemma =
      fst (fst act (fst (snd act .equiv-proof (w , q) .fst .fst) , r)) ≡⟨ cong (λ z -> fst (fst act z)) (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
      fst (fst act (snd act .equiv-proof (w , q) .fst .fst)) ≡⟨ cong fst (equivFun∘invEq act (w , q)) ⟩
      w ∎
  to∘from (w , p) | inl q | inr r =
    ⊥.rec (<-asym (snd (invEq act (w , q))) r)
  to∘from (w , p) | inr q with (n + (w ∸ m)) ≤? n 
  to∘from (w , p) | inr q | inl r =
    ⊥.rec (¬m+n<m r)
  to∘from (w , p) | inr q | inr r =
    ΣPathP (lemma , toPathP (isProp≤ _ p))
    where
    lemma : m + (n + (w ∸ m) ∸ n) ≡ w
    lemma =
      m + (n + (w ∸ m) ∸ n) ≡⟨ cong (m +_) (∸+ (w ∸ m) n) ⟩
      m + (w ∸ m) ≡⟨ +-comm m (w ∸ m) ⟩
      (w ∸ m) + m ≡⟨ ≤-∸-+-cancel q ⟩
      w ∎

  from∘to : ∀ x -> from (to x) ≡ x
  from∘to (w , p) with w ≤? n
  from∘to (w , p) | inl q with fst (equivFun act (w , q)) ≤? m
  from∘to (w , p) | inl q | inl r =
    ΣPathP (lemma , toPathP (isProp≤ _ p))
    where
    lemma : _
    lemma =
      fst (snd act .equiv-proof (fst (fst act (w , q)) , r) .fst .fst) ≡⟨ cong (λ z -> fst (snd act .equiv-proof z .fst .fst)) (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
      fst (snd act .equiv-proof (fst act (w , q)) .fst .fst) ≡⟨ cong fst (invEq∘equivFun act (w , q)) ⟩
      w ∎
  from∘to (w , p) | inl q | inr r =
    ⊥.rec (<-asym (snd (equivFun act (w , q))) r)
  from∘to (w , p) | inr q with (m + (w ∸ n)) ≤? m
  from∘to (w , p) | inr q | inl r =
    ⊥.rec (¬m+n<m r)
  from∘to (w , p) | inr q | inr r =
    ΣPathP (lemma , toPathP (isProp≤ _ p))
    where
    lemma : _
    lemma =
      n + (m + (w ∸ n) ∸ m) ≡⟨ cong (n +_) (∸+ (w ∸ n) m) ⟩
      n + (w ∸ n) ≡⟨ +-comm n (w ∸ n) ⟩
      (w ∸ n) + n ≡⟨ ≤-∸-+-cancel q ⟩
      w ∎

