{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List as L renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.LehmerCode
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
import Cubical.Data.Equality as EQ
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Set.Mon.Array as A
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

SymmAction : ∀ {A : Type ℓ} -> Array A -> Array A -> Type ℓ
SymmAction (n , v) (m , w) = Σ[ σ ∈ Iso (Fin n) (Fin m) ] v ≡ w ∘ σ .fun

_≈_ = SymmAction

symm-length≡ : {n m : ℕ} -> Iso (Fin n) (Fin m) -> n ≡ m 
symm-length≡ {n = n} {m = m} σ = Fin-inj n m (isoToPath σ)

symm-refl : {as : Array A} -> SymmAction as as
symm-refl {as = as} = idIso , refl

symm-sym : {as bs : Array A} -> SymmAction as bs -> SymmAction bs as
symm-sym {as = (n , f)} {bs = (m , g)} (σ , p) =
  invIso σ , congS (g ∘_) (sym (funExt (σ .rightInv)))
           ∙ congS (_∘ σ .inv) (sym p)

symm-trans : {as bs cs : Array A} -> SymmAction as bs -> SymmAction bs cs -> SymmAction as cs
symm-trans {as = (n , f)} {bs = (m , g)} {cs = (o , h)} (σ , p) (τ , q) =
  compIso σ τ , sym
    ((h ∘ τ .fun) ∘ σ .fun ≡⟨ congS (_∘ σ .fun) (sym q) ⟩
    g ∘ σ .fun ≡⟨ sym p ⟩
    f ∎)

Array≡-len : {as bs : Array A} -> as ≡ bs -> as .fst ≡ bs .fst
Array≡-len {as = (n , f)} {bs = (m , g)} p = cong fst p

Fin+-cong : {n m n' m' : ℕ} -> Iso (Fin n) (Fin n') -> Iso (Fin m) (Fin m') -> Iso (Fin (n + m)) (Fin (n' + m'))
Fin+-cong {n} {m} {n'} {m'} σ τ =
  compIso (Fin≅Fin+Fin n m) (compIso (⊎Iso σ τ) (invIso (Fin≅Fin+Fin n' m')))

⊎Iso-eta : {A B A' B' : Type ℓ} {C : Type ℓ'} (f : A' -> C) (g : B' -> C)
        -> (σ : Iso A A') (τ : Iso B B')
        -> ⊎.rec (f ∘ σ .fun) (g ∘ τ .fun) ≡ ⊎.rec f g ∘ ⊎Iso σ τ .fun
⊎Iso-eta f g σ τ i (inl a) = f (σ .fun a)
⊎Iso-eta f g σ τ i (inr b) = g (τ .fun b)

⊎Swap-eta : {A B : Type ℓ} {C : Type ℓ'} (f : A -> C) (g : B -> C)
        -> ⊎.rec g f ∘ ⊎-swap-Iso .fun ≡ ⊎.rec f g
⊎Swap-eta f g i (inl a) = f a
⊎Swap-eta f g i (inr b) = g b

symm-cong : {as bs cs ds : Array A} -> as ≈ bs -> cs ≈ ds -> (as ⊕ cs) ≈ (bs ⊕ ds)
symm-cong {as = n , f} {bs = n' , f'} {m , g} {m' , g'} (σ , p) (τ , q) =
  Fin+-cong σ τ ,
  (
    combine n m f g
  ≡⟨ cong₂ (combine n m) p q ⟩
    combine n m (f' ∘ σ .fun) (g' ∘ τ .fun)
  ≡⟨⟩
    ⊎.rec (f' ∘ σ .fun) (g' ∘ τ .fun) ∘ finSplit n m
  ≡⟨ congS (_∘ finSplit n m) (⊎Iso-eta f' g' σ τ) ⟩
    ⊎.rec f' g' ∘ ⊎Iso σ τ .fun ∘ finSplit n m
  ≡⟨⟩
    ⊎.rec f' g' ∘ idfun _ ∘ ⊎Iso σ τ .fun ∘ finSplit n m
  ≡⟨ congS (λ f -> ⊎.rec f' g' ∘ f ∘ ⊎Iso σ τ .fun ∘ finSplit n m) (sym (funExt (Fin≅Fin+Fin n' m' .rightInv))) ⟩
    ⊎.rec f' g' ∘ (Fin≅Fin+Fin n' m' .fun ∘ Fin≅Fin+Fin n' m' .inv) ∘ ⊎Iso σ τ .fun ∘ finSplit n m
  ≡⟨⟩
    (⊎.rec f' g' ∘ Fin≅Fin+Fin n' m' .fun) ∘ (Fin≅Fin+Fin n' m' .inv ∘ ⊎Iso σ τ .fun ∘ finSplit n m)
  ≡⟨⟩
    combine n' m' f' g' ∘ Fin+-cong σ τ .fun
  ∎)

Fin+-comm : (n m : ℕ) -> Iso (Fin (n + m)) (Fin (m + n))
Fin+-comm n m = compIso (Fin≅Fin+Fin n m) (compIso ⊎-swap-Iso (invIso (Fin≅Fin+Fin m n)))

symm-comm : {as bs : Array A} -> (as ⊕ bs) ≈ (bs ⊕ as)
symm-comm {as = n , f} {bs = m , g} =
  Fin+-comm n m , sym
    (
      ⊎.rec g f ∘ finSplit m n ∘ Fin≅Fin+Fin m n .inv ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun
    ≡⟨⟩
      ⊎.rec g f ∘ (Fin≅Fin+Fin m n .fun ∘ Fin≅Fin+Fin m n .inv) ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun
    ≡⟨ congS (λ h -> ⊎.rec g f ∘ h ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun) (funExt (Fin≅Fin+Fin m n .rightInv)) ⟩
      ⊎.rec g f ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun
    ≡⟨ congS (_∘ Fin≅Fin+Fin n m .fun) (⊎Swap-eta f g) ⟩
      ⊎.rec f g ∘ Fin≅Fin+Fin n m .fun
    ∎)

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f : A -> 𝔜 .car) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f♯-hom = A.Free.♯-isMonHom isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

  f♯ : Array A -> 𝔜 .car
  f♯ = f♯-hom .fst

  fin-id-iso : ∀ {n m} -> n ≡ m -> Iso (Fin n) (Fin m)
  fin-id-iso {n = n} {m = m} p =
    iso
      (λ (w , q) -> w , subst (w <_) p q)
      (λ (w , q) -> w , subst (w <_) (sym p) q)
      (λ (w , q) -> ΣPathP (refl , substSubst⁻ (w <_) p q))
      (λ (w , q) -> ΣPathP (refl , substSubst⁻ (w <_) (sym p) q))

  permuteArray : ∀ n (zs : Fin n -> A) (aut : LehmerCode n) -> Array A
  permuteArray .zero zs [] = 0 , ⊥.rec ∘ ¬Fin0
  permuteArray .(suc _) zs (p ∷ ps) = η (zs p) ⊕ permuteArray _ (zs ∘ fsuc) ps

  f♯-hom-⊕ : (as bs : Array A) -> f♯ (as ⊕ bs) ≡ f♯ as 𝔜.⊕ f♯ bs
  f♯-hom-⊕ as bs =
    f♯ (as ⊕ bs) ≡⟨ sym ((f♯-hom .snd) M.`⊕ (lookup (as ∷ₗ bs ∷ₗ []))) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f♯ (lookup (as ∷ₗ bs ∷ₗ []) w))) ≡⟨ 𝔜.⊕-eta (lookup (as ∷ₗ bs ∷ₗ [])) f♯ ⟩
    _ ∎

  -- TODO: get rid of this TERMINATING pragma
  {-# TERMINATING #-}  
  permuteInvariant : ∀ n (zs : Fin n -> A) (aut : LehmerCode n) -> f♯ (permuteArray n zs aut) ≡ f♯ (n , zs)
  permuteInvariant .zero zs [] =
    congS f♯ (ΣPathP {x = 0 , zs} {y = permuteArray 0 zs []} (refl , funExt (⊥.rec ∘ ¬Fin0)))
  permuteInvariant .1 zs (x ∷ []) =
    congS f♯ (ΣPathP {x = permuteArray 1 zs (x ∷ [])} {y = 1 , zs} (refl , funExt lemma))
    where
    lemma : _
    lemma (k , p) =
      ⊎.rec (λ _ → zs x) _ (finSplit 1 0 (k , p)) ≡⟨ congS (⊎.rec (λ _ → zs x) _) (finSplit-beta-inl k p p) ⟩
      zs x ≡⟨ congS zs (isContr→isProp isContrFin1 x (k , p)) ⟩
      zs (k , p) ∎
  permuteInvariant .(suc (suc _)) zs ((l , p) ∷ y ∷ aut) with l
  ... | zero =
          f♯ (η (zs (zero , p)) ⊕ (η (zs (fsuc y)) ⊕ permuteArray _ (zs ∘ fsuc ∘ fsuc) aut))
        ≡⟨ f♯-hom-⊕ (η (zs (zero , p))) (η (zs (fsuc y)) ⊕ permuteArray _ (zs ∘ fsuc ∘ fsuc) aut) ⟩
          f♯ (η (zs (zero , p))) 𝔜.⊕ f♯ (η (zs (fsuc y)) ⊕ permuteArray _ (zs ∘ fsuc ∘ fsuc) aut)
        ≡⟨ congS (f♯ (η (zs (zero , p))) 𝔜.⊕_) (permuteInvariant (suc _) (zs ∘ fsuc) (y ∷ aut)) ⟩
          f♯ (η (zs (zero , p))) 𝔜.⊕ f♯ (_ , zs ∘ fsuc)
        ≡⟨ sym (f♯-hom-⊕ (η (zs (zero , p))) (_ , zs ∘ fsuc)) ⟩
          f♯ (η (zs (zero , p)) ⊕ (_ , zs ∘ fsuc))
        ≡⟨ congS (λ z -> f♯ (η (zs z) ⊕ (_ , zs ∘ fsuc))) (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
          f♯ (η (zs fzero) ⊕ (_ , zs ∘ fsuc))
        ≡⟨ congS f♯ (η+fsuc zs) ⟩
          f♯ (_ , zs)
        ∎
  ... | suc l' = {!   !}

  symm-resp-f♯ : {as bs : Array A} -> SymmAction as bs -> f♯ as ≡ f♯ bs
  symm-resp-f♯ {as = n , g} {bs = m , h} (σ , p) =
    f♯ (n , g) ≡⟨ congS (λ z -> f♯ (n , z)) p ⟩
    f♯ (n , h ∘ σ .fun) ≡⟨ congS f♯ (ΣPathP (n≡m , toPathP (funExt lemma))) ⟩
    f♯ (m , h ∘ σ .fun ∘ (fin-id-iso (sym n≡m)) .fun) ≡⟨⟩
    f♯ (m , h ∘ (compIso (fin-id-iso (sym n≡m)) σ) .fun) ≡⟨ {!   !} ⟩
    f♯ (permuteArray m h (encode (isoToEquiv (compIso (fin-id-iso (sym n≡m)) σ)))) ≡⟨⟩
    {!  !}
    where
    n≡m : n ≡ m
    n≡m = symm-length≡ σ

    lemma : _
    lemma (w , q) =
      _ ≡⟨ sym (transport-filler _ _) ⟩
      h (σ .fun (subst Fin (sym n≡m) (w , q))) ∎

module _ {ℓ} (A : Type ℓ) where
  open import Cubical.Relation.Binary
  module P = BinaryRelation {A = Array A} SymmAction
  open isPermRel

  isPermRelPerm : isPermRel arrayDef (SymmAction {A = A})
  P.isEquivRel.reflexive (isEquivRel isPermRelPerm) _ = symm-refl
  P.isEquivRel.symmetric (isEquivRel isPermRelPerm) _ _ = symm-sym
  P.isEquivRel.transitive (isEquivRel isPermRelPerm) _ _ cs = symm-trans {cs = cs}
  isCongruence isPermRelPerm {as} {bs} {cs} {ds} p q = symm-cong p q
  isCommutative isPermRelPerm = symm-comm
  resp-♯ isPermRelPerm {isSet𝔜 = isSet𝔜} 𝔜-cmon f p = symm-resp-f♯ isSet𝔜 𝔜-cmon f p
 