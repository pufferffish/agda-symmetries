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

  f♯-hom-⊕ : (as bs : Array A) -> f♯ (as ⊕ bs) ≡ f♯ as 𝔜.⊕ f♯ bs
  f♯-hom-⊕ as bs =
    f♯ (as ⊕ bs) ≡⟨ sym ((f♯-hom .snd) M.`⊕ (lookup (as ∷ₗ bs ∷ₗ []))) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f♯ (lookup (as ∷ₗ bs ∷ₗ []) w))) ≡⟨ 𝔜.⊕-eta (lookup (as ∷ₗ bs ∷ₗ [])) f♯ ⟩
    _ ∎

  n<1→n≡0 : ∀ {n} -> n < 1 -> 0 ≡ n
  n<1→n≡0 {n = zero} p = refl
  n<1→n≡0 {n = suc n} p = ⊥.rec (¬-<-zero (pred-≤-pred p))

  fpred : ∀ {n} -> Fin (suc (suc n)) -> Fin (suc n)
  fpred (zero , p) = fzero
  fpred (suc w , p) = w , pred-≤-pred p

  fsuc∘fpred : ∀ {n} -> (x : Fin (suc (suc n))) -> ¬ x ≡ fzero -> fsuc (fpred x) ≡ x
  fsuc∘fpred (zero , p) q = ⊥.rec (q (Σ≡Prop (λ _ -> isProp≤) refl))
  fsuc∘fpred (suc k , p) q = Σ≡Prop (λ _ -> isProp≤) refl

  fpred∘fsuc : ∀ {n} -> (x : Fin (suc n)) -> fpred (fsuc x) ≡ x
  fpred∘fsuc (k , p) = Σ≡Prop (λ _ -> isProp≤) refl

  autInvIs0 : ∀ {n} -> (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
            -> aut .fun fzero ≡ fzero
            -> inv aut fzero ≡ fzero
  autInvIs0 aut q =
    inv aut fzero ≡⟨ congS (inv aut) (sym q) ⟩
    inv aut (aut .fun fzero) ≡⟨ aut .leftInv fzero ⟩
    fzero ∎

  autSucNot0 : ∀ {n} -> (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
            -> (x : Fin (suc n))
            -> aut .fun fzero ≡ fzero
            -> ¬ aut .fun (fsuc x) ≡ fzero
  autSucNot0 aut x p q =
    let r = isoFunInjective aut _ _ (p ∙ sym q)
    in znots (cong fst r)

  punchOutZero : ∀ {n} (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) -> aut .fun fzero ≡ fzero
                -> Iso (Fin (suc n)) (Fin (suc n))
  punchOutZero {n = n} aut p =
    iso (punch aut) (punch (invIso aut)) (punch∘punch aut p) (punch∘punch (invIso aut) (autInvIs0 aut p)) 
    where
    punch : Iso (Fin (suc (suc n))) (Fin (suc (suc n))) -> _
    punch aut = fpred ∘ aut .fun ∘ fsuc
    punch∘punch : (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
                -> aut .fun fzero ≡ fzero
                -> (x : Fin (suc n))
                -> punch aut (punch (invIso aut) x) ≡ x
    punch∘punch aut p x =
        punch aut (punch (invIso aut) x)
      ≡⟨⟩
        (fpred (aut .fun ((fsuc ∘ fpred) (aut .inv (fsuc x)))))
      ≡⟨ congS (fpred ∘ aut .fun) (fsuc∘fpred (aut .inv (fsuc x)) (autSucNot0 (invIso aut) x (autInvIs0 aut p))) ⟩
        (fpred (aut .fun (aut .inv (fsuc x))))
      ≡⟨ congS fpred (aut .rightInv (fsuc x)) ⟩
        (fpred (fsuc x))
      ≡⟨ fpred∘fsuc x ⟩
        x ∎

  permuteInvariant' : ∀ n tag -> n ≡ tag -- to help termination checker
                  -> (zs : Fin n -> A) (aut : Iso (Fin n) (Fin n))
                  -> f♯ (n , zs ∘ aut .fun) ≡ f♯ (n , zs)
  permuteInvariant' (suc (suc n)) zero tag≡  zs aut =
    ⊥.rec (snotz tag≡)
  permuteInvariant' zero _ _ zs aut =
    congS f♯ (ΣPathP {x = 0 , zs ∘ aut .fun} {y = 0 , zs} (refl , funExt (⊥.rec ∘ ¬Fin0)))
  permuteInvariant' (suc zero) _ _ zs aut =
    congS f♯ (ΣPathP {x = 1 , zs ∘ aut .fun} {y = 1 , zs} (refl , lemma))
    where
    lemma : _
    lemma =
      zs ∘ aut .fun ≡⟨ congS (zs ∘_) (isContr→isProp (isContrΠ (λ _ -> isContrFin1)) (aut .fun) (idfun _)) ⟩
      zs ∘ idfun _ ≡⟨⟩
      zs ∎
  permuteInvariant' (suc (suc n)) (suc tag) tag≡ zs aut with aut .fun fzero | inspect (aut .fun) fzero
  ... | zero , p | [ aut-path ]ᵢ  =
      f (zs (zero , p)) 𝔜.⊕ (f (zs (aut .fun (1 , (n , _)))) 𝔜.⊕ f♯ (n , (λ x → zs (aut .fun (suc (suc (fst x)) , fst (snd x) , _)))))
    ≡⟨ congS (λ z -> f (zs (zero , p)) 𝔜.⊕ (z 𝔜.⊕ f♯ (n , (λ x → zs (aut .fun (suc (suc (fst x)) , fst (snd x) , _)))))) (sym (𝔜.unitr _)) ⟩
      f (zs (zero , p)) 𝔜.⊕ (f♯ (η (zs (aut .fun (1 , (n , _))))) 𝔜.⊕ f♯ (n , (λ x → zs (aut .fun (suc (suc (fst x)) , fst (snd x) , _)))))
    ≡⟨ congS (f (zs (zero , p)) 𝔜.⊕_) (sym (f♯-hom-⊕ (η (zs (aut .fun (1 , (n , _))))) ((n , (λ x → zs (aut .fun (suc (suc (fst x)) , fst (snd x) , _))))))) ⟩
      f (zs (zero , p)) 𝔜.⊕ (f♯ (η (zs (aut .fun (1 , (n , _)))) ⊕ (n , (λ x → zs (aut .fun (suc (suc (fst x)) , fst (snd x) , _))))))
    ≡⟨ congS (λ z -> f (zs (zero , p)) 𝔜.⊕ (f♯ z)) (ΣPathP {x = pattern0} {y = (suc n) , zs ∘ fsuc ∘ punchOutZero aut aut-0≡0 .fun} (refl , toPathP (funExt lemma))) ⟩
      f (zs (zero , p)) 𝔜.⊕ f♯ ((suc n) , zs ∘ fsuc ∘ punchOutZero aut aut-0≡0 .fun)
    ≡⟨ cong₂ 𝔜._⊕_ (sym (𝔜.unitr _)) (permuteInvariant' (suc n) tag (injSuc tag≡) (zs ∘ fsuc) (punchOutZero aut aut-0≡0)) ⟩
      f♯ (η (zs (zero , p))) 𝔜.⊕ f♯ ((suc n) , zs ∘ fsuc)
    ≡⟨ sym (f♯-hom-⊕ (η (zs (zero , p))) ((suc n) , zs ∘ fsuc)) ⟩
      f♯ (η (zs (zero , p)) ⊕ ((suc n) , zs ∘ fsuc))
    ≡⟨ congS (λ z -> f♯ (η (zs z) ⊕ ((suc n) , zs ∘ fsuc))) (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
      f♯ (η (zs fzero) ⊕ ((suc n) , zs ∘ fsuc))
    ≡⟨ congS f♯ (η+fsuc zs) ⟩
      f♯ (suc (suc n) , zs) ∎
    where
    aut-0≡0 : aut .fun fzero ≡ fzero
    aut-0≡0 =
      aut .fun fzero ≡⟨ Σ≡Prop (λ _ -> isProp≤) refl ⟩
      aut .fun (0 , _) ≡⟨ aut-path ⟩
      (0 , p) ≡⟨ Σ≡Prop (λ _ -> isProp≤) refl ⟩
      fzero ∎
    pattern0 : _
    pattern0 = (η (zs (aut .fun (1 , (n , _)))) ⊕ (n , (λ x → zs (aut .fun (suc (suc (fst x)) , fst (snd x) , _)))))
    lemma : _
    lemma (k , q) with k ≤? 1
    ... | inl r =
        _
      ≡⟨ sym (transport-filler _ _) ⟩
        ⊎.rec _ _ (finSplit 1 n (k , _))
      ≡⟨ congS (⊎.rec _ _) (finSplit-beta-inl k r _) ⟩
        zs (aut .fun (1 , _))
      ≡⟨ congS zs (sym (fsuc∘fpred (aut .fun fone) (autSucNot0 aut fzero aut-0≡0))) ⟩
        zs (fsuc (fpred (aut .fun fone)))
      ≡⟨ congS (zs ∘ fsuc ∘ fpred ∘ aut .fun ∘ fsuc) (Σ≡Prop (λ _ -> isProp≤) (n<1→n≡0 r)) ⟩
        zs (fsuc (fpred (aut .fun (fsuc (k , q)))))
      ≡⟨⟩
        zs (fsuc (punchOutZero aut aut-0≡0 .fun (k , q))) ∎
    ... | inr r =
        _
      ≡⟨ sym (transport-filler _ _) ⟩
        ⊎.rec _ _ (finSplit 1 n (k , _))
      ≡⟨ congS (⊎.rec _ _) (finSplit-beta-inr k _ r k-1<n) ⟩
        zs (aut .fun (suc (suc (k ∸ 1)) , _))
      ≡⟨ congS (zs ∘ aut .fun) (Σ≡Prop (λ _ -> isProp≤) (congS suc suck-1<k)) ⟩
        zs (aut .fun (fsuc (k , q)))
      ≡⟨ congS zs (sym (fsuc∘fpred (aut .fun (fsuc (k , q))) (autSucNot0 aut (k , q) aut-0≡0))) ⟩
        zs (fsuc (fpred (aut .fun (fsuc (k , q)))))
      ≡⟨⟩
        zs (fsuc (punchOutZero aut aut-0≡0 .fun (k , q))) ∎
      where
      k-1<n : k ∸ 1 < n
      k-1<n = ∸-<-lemma 1 n k q r
      suck-1<k : suc (k ∸ 1) ≡ k
      suck-1<k =
        suc (k ∸ 1) ≡⟨ +-comm 1 _ ⟩
        (k ∸ 1) + 1 ≡⟨ ≤-∸-+-cancel r ⟩
        k ∎
  ... | suc k , p | [ aut-path ]ᵢ = {!   !}

  permuteInvariant : ∀ n (zs : Fin n -> A) (aut : Iso (Fin n) (Fin n)) -> f♯ (n , zs ∘ aut .fun) ≡ f♯ (n , zs)
  permuteInvariant n = permuteInvariant' n n refl

  symm-resp-f♯ : {as bs : Array A} -> SymmAction as bs -> f♯ as ≡ f♯ bs
  symm-resp-f♯ {as = n , g} {bs = m , h} (σ , p) =
      f♯ (n , g)
    ≡⟨ congS (λ z -> f♯ (n , z)) p ⟩
      f♯ (n , h ∘ σ .fun)
    ≡⟨ congS f♯ (ΣPathP (n≡m , toPathP (funExt lemma))) ⟩
      f♯ (m , h ∘ σ .fun ∘ (fin-id-iso (sym n≡m)) .fun)
    ≡⟨⟩
      f♯ (m , h ∘ (compIso (fin-id-iso (sym n≡m)) σ) .fun)
    ≡⟨ permuteInvariant m h (compIso (fin-id-iso (sym n≡m)) σ) ⟩
      f♯ (m , h) ∎
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
    