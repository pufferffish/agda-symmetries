{-# OPTIONS --cubical #-}

-- Taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.AFunc where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.SumFin as F
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as ⊥
import Cubical.Data.List as L
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

SymAct : ∀ {A : Type ℓ} -> (n : ℕ) -> (Fin n -> A) -> (Fin n -> A) -> Type ℓ
SymAct n v w = ∃[ σ ∈ (Fin n ≃ Fin n) ] v ≡ w ∘ (σ .fst)

AFunc : Type ℓ -> Type ℓ
AFunc A = Σ[ n ∈ ℕ ] (Fin n -> A) Q./ SymAct n

_∷_ : {n : ℕ} {Y : Fin (suc n) -> Type ℓ}
  -> (Y F.fzero)
  -> ((k : Fin n) -> Y (F.fsuc k))
  -> ((k : Fin (suc n)) -> Y k)
v₀ ∷ vₙ = Sum.elim (const v₀) vₙ

box-cons : ∀ {n} {Y : Fin (suc n) -> Type ℓ} -> ∥ Y F.fzero ∥₂ -> ∥ ((k : Fin n) -> Y (F.fsuc k)) ∥₂ -> ∥ ((k : Fin (suc n)) -> Y k) ∥₂
box-cons = ST.rec2 ST.isSetSetTrunc (λ x y -> ∣ x ∷ y ∣₂)

box : ∀ {n} {Y : Fin n -> Type ℓ} -> ((k : Fin n) -> ∥ Y k ∥₂) -> ∥ ((k : Fin n) -> Y k) ∥₂
box {n = zero} v = ∣ (λ ()) ∣₂
box {n = suc n} v = box-cons (v F.fzero) (box (v ∘ F.fsuc))

unbox : ∀ {n} {Y : Fin n -> Type ℓ} -> ∥ ((k : Fin n) -> Y k) ∥₂ -> ((k : Fin n) -> ∥ Y k ∥₂)
unbox v k = ST.rec squash₂ (λ x -> ∣ x k ∣₂) v

box-compute : ∀ {n} {Y : Fin n -> Type ℓ} -> (v : (k : Fin n) -> Y k) -> box (λ k -> ∣ v k ∣₂) ≡ ∣ v ∣₂
box-compute {n = 0} v = cong ∣_∣₂ (funExt λ ())
box-compute {n = suc n} {Y = Y} v =
  box-cons (∣ v F.fzero ∣₂) (box (∣_∣₂ ∘ v ∘ F.fsuc))
    ≡⟨ cong (box-cons ∣ v F.fzero ∣₂) (box-compute (v ∘ F.fsuc)) ⟩
  box-cons (∣ v F.fzero ∣₂) ∣ v ∘ F.fsuc ∣₂
    ≡⟨ cong ∣_∣₂ (funExt (Sum.elim (λ _ -> refl) λ _ -> refl)) ⟩
  ∣ v ∣₂ ∎

box∘unbox : ∀ {n} {Y : Fin n -> Type ℓ} -> (v : ∥ ((k : Fin n) -> Y k) ∥₂) -> box (unbox v) ≡ v
box∘unbox {n = n} {Y = Y} = ST.elim (λ _ -> ST.isSetPathImplicit) box-compute

unbox∘box : ∀ {n} {Y : Fin n -> Type ℓ} -> (v : (k : Fin n) -> ∥ Y k ∥₂) -> unbox (box v) ≡ v
unbox∘box {n = zero} v = funExt λ ()
unbox∘box {n = suc n} {Y = Y} v =
  funExt
    (Sum.elim
      (λ _ -> unfold-once F.fzero ∙ map2IdRight v₀ (box vₙ))
      (λ k ->
        _ ≡⟨ unfold-once (F.fsuc k) ⟩
        _ ≡⟨ map2ConstLeft _ v₀ (box vₙ) ⟩
        _ ≡⟨ funExt⁻ (unbox∘box {n = n} vₙ) k ⟩
        _ ∎
      )
    )
  where
  v₀ : ∥ Y F.fzero ∥₂
  v₀ = v F.fzero

  vₙ : (k : Fin n) -> ∥ Y (F.fsuc k) ∥₂
  vₙ = v ∘ F.fsuc

  map2' : ∀ {ℓx ℓy ℓz} {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz}
    -> (f : X -> Y -> Z)
    -> ∥ X ∥₂ -> ∥ Y ∥₂ -> ∥ Z ∥₂
  map2' f = ST.rec2 ST.isSetSetTrunc λ x y -> ∣ f x y ∣₂

  rec∘map2 : ∀ {ℓx ℓy ℓz ℓw} {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz} {W : Type ℓw}
    -> (setZ : isSet Z)
    -> (f : X -> W -> Y)
    -> (g : Y -> Z)
    -> (x : ∥ X ∥₂)
    -> (w : ∥ W ∥₂)
    -> ST.rec setZ g (map2' f x w) ≡ ST.rec2 setZ (λ x w -> g (f x w)) x w
  rec∘map2 {Z = Z} setZ f g = ST.elim2 (λ _ _ -> isProp→isSet (setZ _ _)) λ _ _ -> refl

  map2IdRight : ∀ {ℓx ℓw} {X : Type ℓx} {W : Type ℓw}
    -> (x : ∥ X ∥₂)
    -> (w : ∥ W ∥₂)
    -> map2' (λ x w -> x) x w ≡ x
  map2IdRight = ST.elim2 (λ _ _ -> ST.isSetPathImplicit) (λ _ _ -> refl)

  unfold-once : ∀ k -> unbox (box v) k ≡ ST.rec2 ST.isSetSetTrunc (λ y₀ yₙ -> ∣ _ ∣₂) v₀ (box vₙ)
  unfold-once k = rec∘map2 ST.isSetSetTrunc _ (λ v -> ∣ v k ∣₂) v₀ (box vₙ)

  map2ConstLeft : ∀ {ℓx ℓz ℓw} {X : Type ℓx} {Z : Type ℓz} {W : Type ℓw}
    -> (f : W -> Z)
    -> (x : ∥ X ∥₂)
    -> (w : ∥ W ∥₂)
    -> map2' (λ x w -> f w) x w ≡ ST.map f w
  map2ConstLeft f = ST.elim2 (λ _ _ -> isProp→isSet (ST.isSetSetTrunc _ _)) (λ _ _ -> refl)

finChoiceEquiv : ∀ {n} {Y : Fin n -> Type ℓ} -> ((k : Fin n) -> ∥ Y k ∥₂) ≃ ∥ ((k : Fin n) -> Y k) ∥₂
finChoiceEquiv = isoToEquiv (iso box unbox box∘unbox unbox∘box)

  