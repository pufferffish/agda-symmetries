{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
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
⊎Iso-eta f g σ τ = ⊎-eta (⊎.rec f g ∘ ⊎Iso σ τ .fun) refl refl

⊎Swap-eta : {A B : Type ℓ} {C : Type ℓ'} (f : A -> C) (g : B -> C)
        -> ⊎.rec f g ≡ ⊎.rec g f ∘ ⊎-swap-Iso .fun
⊎Swap-eta f g = ⊎-eta (⊎.rec g f ∘ ⊎-swap-Iso .fun) refl refl

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
  ≡⟨ congS (\h -> ⊎.rec f' g' ∘ h ∘ ⊎Iso σ τ .fun ∘ finSplit n m) (sym (funExt (Fin≅Fin+Fin n' m' .rightInv))) ⟩
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
    ≡⟨ congS (_∘ Fin≅Fin+Fin n m .fun) (sym (⊎Swap-eta f g)) ⟩
      ⊎.rec f g ∘ Fin≅Fin+Fin n m .fun
    ∎)

fpred : ∀ {n} -> Fin (suc (suc n)) -> Fin (suc n)
fpred (zero , p) = fzero
fpred (suc w , p) = w , pred-≤-pred p

fsuc∘fpred : ∀ {n} -> (x : Fin (suc (suc n))) -> ¬ x ≡ fzero -> fsuc (fpred x) ≡ x
fsuc∘fpred (zero , p) q = ⊥.rec (q (Fin-fst-≡ refl))
fsuc∘fpred (suc k , p) q = Fin-fst-≡ refl

fpred∘fsuc : ∀ {n} -> (x : Fin (suc n)) -> fpred (fsuc x) ≡ x
fpred∘fsuc (k , p) = Fin-fst-≡ refl

isoFunInv : ∀ {A B : Type ℓ} {x y} -> (σ : Iso A B) -> σ .fun x ≡ y -> σ .inv y ≡ x
isoFunInv σ p = congS (σ .inv) (sym p) ∙ σ .leftInv _

isoFunInvContra : ∀ {A B : Type ℓ} {x y z} -> (σ : Iso A B) -> σ .fun x ≡ y -> ¬ (z ≡ y) -> ¬ (σ .inv z ≡ x)
isoFunInvContra σ p z≠y q = z≠y (sym (σ .rightInv _) ∙ congS (σ .fun) q ∙ p)

autInvIs0 : ∀ {n} -> (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
          -> aut .fun fzero ≡ fzero -> aut .inv fzero ≡ fzero
autInvIs0 = isoFunInv

autSucNot0 : ∀ {n} -> (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
          -> (x : Fin (suc n)) -> aut .fun fzero ≡ fzero -> ¬ aut .fun (fsuc x) ≡ fzero
autSucNot0 aut x p = isoFunInvContra (invIso aut) (isoFunInv aut p) (snotz ∘ congS fst)

punchOutZero : ∀ {n} (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) -> aut .fun fzero ≡ fzero
              -> Iso (Fin (suc n)) (Fin (suc n))
punchOutZero {n = n} aut p =
  iso (punch aut) (punch (invIso aut)) (punch∘punch aut p) (punch∘punch (invIso aut) (autInvIs0 aut p)) 
  where
  punch : Iso (Fin (suc (suc n))) (Fin (suc (suc n))) -> Fin (suc n) -> Fin (suc n)
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

punchOutZero≡fsuc : ∀ {n} (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) -> (aut-0≡0 : aut .fun fzero ≡ fzero)
                  -> (w : Fin (suc n)) -> aut .fun (fsuc w) ≡ fsuc (punchOutZero aut aut-0≡0 .fun w)
punchOutZero≡fsuc aut aut-0≡0 w = sym (fsuc∘fpred _ (autSucNot0 aut w aut-0≡0))

finSubst : ∀ {n m} -> n ≡ m -> Fin n -> Fin m
finSubst {n = n} {m = m} p (k , q) = k , (subst (k <_) p q)

finIso : ∀ {n m} -> n ≡ m -> Iso (Fin n) (Fin m)
finIso {n = n} {m = m} p = iso
  (finSubst p)
  (finSubst (sym p))
  (λ (k , q) -> Fin-fst-≡ refl)
  (λ (k , q) -> Fin-fst-≡ refl)

symm-fsuc-on-0 : ∀ n m
          -> (f : Fin (suc (suc n)) -> A) (g : Fin (suc (suc m)) -> A)
          -> (r : SymmAction (suc (suc n) , f) (suc (suc m) , g))
          -> (r .fst) .fun fzero ≡ fzero
          -> SymmAction (suc n , f ∘ fsuc) (suc m , g ∘ fsuc)
symm-fsuc-on-0 n m f g (σ , p) q =
  compIso (finIso (injSuc (symm-length≡ σ))) (punchOutZero τ lemma-α) , sym (funExt lemma-β)
  where
  τ : _
  τ = compIso (finIso (sym (symm-length≡ σ))) σ
  lemma-α : _
  lemma-α =
    σ .fun (finSubst (sym (symm-length≡ σ)) fzero) ≡⟨⟩
    σ .fun (0 , _) ≡⟨ congS (σ .fun) (Fin-fst-≡ refl) ⟩
    σ .fun fzero ≡⟨ q ⟩
    fzero ∎
  lemma-β : _
  lemma-β (k , r) =
      g (fsuc ((punchOutZero τ lemma-α) .fun ((finIso (injSuc (symm-length≡ σ))) .fun (k , r))))
    ≡⟨⟩
      g (fsuc ((punchOutZero τ lemma-α) .fun (k , _)))
    ≡⟨ congS g (sym (punchOutZero≡fsuc τ lemma-α (k , _))) ⟩
      g (τ .fun (fsuc (k , _)))
    ≡⟨ congS (g ∘ σ .fun) (Fin-fst-≡ refl) ⟩
      g (σ .fun (fsuc (k , r)))
    ≡⟨ congS (λ h -> h (fsuc (k , r))) (sym p) ⟩
      f (fsuc (k , r)) ∎

module _ {n} (aut : Iso (Fin (suc n)) (Fin (suc n))) where
  private
    m : ℕ
    m = suc n

    cutoff : ℕ
    cutoff = (aut .inv fzero) .fst

    cutoff< : cutoff < m
    cutoff< = (aut .inv fzero) .snd

    cutoff+- : cutoff + (m ∸ cutoff) ≡ m
    cutoff+- = ∸-lemma (<-weaken cutoff<)

    0<m-cutoff : 0 < m ∸ cutoff
    0<m-cutoff = n∸l>0 m cutoff cutoff<

  swapAut : Iso (Fin (suc n)) (Fin (suc n))
  swapAut = compIso (finIso (sym cutoff+- ∙ +-comm cutoff _)) (compIso (Fin+-comm (m ∸ cutoff) cutoff) (compIso (finIso cutoff+-) aut))

  swapAut0≡0 : swapAut .fun fzero ≡ fzero
  swapAut0≡0 =
      aut .fun (finSubst cutoff+- (⊎.rec finCombine-inl finCombine-inr (fun ⊎-swap-Iso (finSplit (m ∸ cutoff) cutoff (0 , _)))))
    ≡⟨ congS (λ z -> aut .fun (finSubst cutoff+- (⊎.rec (finCombine-inl {m = cutoff}) (finCombine-inr {m = cutoff}) (fun ⊎-swap-Iso z)))) (finSplit-beta-inl 0 0<m-cutoff _) ⟩
      aut .fun (aut .inv fzero .fst + 0 , _)
    ≡⟨ congS (aut .fun) (Fin-fst-≡ (+-zero (aut .inv (0 , suc-≤-suc zero-≤) .fst) ∙ congS (fst ∘ aut .inv) (Fin-fst-≡ refl))) ⟩
      aut .fun (aut .inv fzero)
    ≡⟨ aut .rightInv fzero ⟩
      fzero ∎

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f : A -> 𝔜 .car) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f♯-hom = A.Free.♯-isMonHom isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

  f♯ : Array A -> 𝔜 .car
  f♯ = f♯-hom .fst

  f♯-hom-⊕ : (as bs : Array A) -> f♯ (as ⊕ bs) ≡ f♯ as 𝔜.⊕ f♯ bs
  f♯-hom-⊕ as bs =
    f♯ (as ⊕ bs) ≡⟨ sym ((f♯-hom .snd) M.`⊕ ⟪ as ⨾ bs ⟫) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f♯ (⟪ as ⨾ bs ⟫ w))) ≡⟨ 𝔜.⊕-eta ⟪ as ⨾ bs ⟫ f♯ ⟩
    f♯ as 𝔜.⊕ f♯ bs ∎

  f♯-comm : (as bs : Array A) -> f♯ (as ⊕ bs) ≡ f♯ (bs ⊕ as)
  f♯-comm as bs =
    f♯ (as ⊕ bs) ≡⟨ f♯-hom-⊕ as bs ⟩
    f♯ as 𝔜.⊕ f♯ bs ≡⟨ 𝔜.comm (f♯ as) (f♯ bs) ⟩
    f♯ bs 𝔜.⊕ f♯ as ≡⟨ sym (f♯-hom-⊕ bs as) ⟩
    f♯ (bs ⊕ as) ∎

  swapAutToAut : ∀ {n} (zs : Fin (suc (suc n)) -> A) (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
               -> f♯ (suc (suc n) , zs ∘ swapAut aut .fun) ≡ f♯ (suc (suc n) , zs ∘ aut .fun)
  swapAutToAut {n = n} zs aut =
      f♯ (m , zs ∘ swapAut aut .fun)
    ≡⟨ congS f♯ (ΣPathP {x = m , zs ∘ swapAut aut .fun} (sym cutoff+- ∙ +-comm cutoff _ , toPathP (funExt lemma-α))) ⟩
      f♯ (((m ∸ cutoff) , (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inr))
        ⊕ (cutoff , (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inl)))
    ≡⟨ f♯-comm ((m ∸ cutoff) , (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inr)) _ ⟩
      f♯ ((cutoff , (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inl))
        ⊕ ((m ∸ cutoff) , (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inr)))
    ≡⟨ congS f♯ (ΣPathP {x = cutoff + (m ∸ cutoff) , _} {y = m , zs ∘ aut .fun} (cutoff+- , toPathP (funExt lemma-β))) ⟩
      f♯ (m , zs ∘ aut .fun) ∎
    where
    m : ℕ
    m = suc (suc n)

    cutoff : ℕ
    cutoff = (aut .inv fzero) .fst

    cutoff< : cutoff < m
    cutoff< = (aut .inv fzero) .snd

    cutoff+- : cutoff + (m ∸ cutoff) ≡ m
    cutoff+- = ∸-lemma (<-weaken cutoff<)

    lemma-α : _
    lemma-α (k , p) = ⊎.rec
      (λ k<m∸cutoff ->
          _
        ≡⟨ sym (transport-filler _ _) ⟩  
          zs (aut .fun (finSubst cutoff+- (⊎.rec finCombine-inl finCombine-inr (fun ⊎-swap-Iso (finSplit (m ∸ cutoff) cutoff (k , _))))))
        ≡⟨ congS (λ z -> zs (aut .fun (finSubst cutoff+- (⊎.rec (finCombine-inl {m = cutoff}) finCombine-inr (fun ⊎-swap-Iso z))))) (finSplit-beta-inl k k<m∸cutoff _) ⟩
          zs (aut .fun (cutoff + k , _))
        ≡⟨ congS (zs ∘ aut .fun) (Fin-fst-≡ refl) ⟩
          zs (aut .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inr (k , k<m∸cutoff)))))
        ≡⟨⟩
          ⊎.rec
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (inl (k , k<m∸cutoff))
        ≡⟨ congS (⊎.rec _ _) (sym (finSplit-beta-inl k k<m∸cutoff p)) ⟩
          ⊎.rec
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (finSplit (m ∸ cutoff) cutoff (k , p))
      ∎)
      (λ m∸cutoff≤k ->
          _
        ≡⟨ sym (transport-filler _ _) ⟩  
          zs (aut .fun (finSubst cutoff+- (⊎.rec finCombine-inl finCombine-inr (fun ⊎-swap-Iso (finSplit (m ∸ cutoff) cutoff (k , _))))))
        ≡⟨ congS (λ z -> zs (aut .fun (finSubst cutoff+- (⊎.rec (finCombine-inl {m = cutoff}) finCombine-inr (fun ⊎-swap-Iso z))))) (finSplit-beta-inr k _ m∸cutoff≤k (∸-<-lemma (m ∸ cutoff) cutoff k p m∸cutoff≤k)) ⟩
          zs (aut .fun (finSubst cutoff+- (finCombine-inl (k ∸ (m ∸ cutoff) , ∸-<-lemma (m ∸ cutoff) cutoff k p m∸cutoff≤k))))  
        ≡⟨ congS (zs ∘ aut .fun ∘ finSubst cutoff+-) (Fin-fst-≡ refl) ⟩
          zs (aut .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inl (k ∸ (m ∸ cutoff) , ∸-<-lemma (m ∸ cutoff) cutoff k p m∸cutoff≤k)))))
        ≡⟨ congS (⊎.rec _ _) (sym (finSplit-beta-inr k p m∸cutoff≤k (∸-<-lemma (m ∸ cutoff) cutoff k p m∸cutoff≤k))) ⟩
          ⊎.rec
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (finSplit (m ∸ cutoff) cutoff (k , p))
      ∎)
      (k ≤? (m ∸ cutoff))
    
    lemma-β : _
    lemma-β (k , p) = ⊎.rec
      (λ k<cutoff ->
          _
        ≡⟨ sym (transport-filler _ _) ⟩
          ⊎.rec
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (finSplit cutoff (m ∸ cutoff) (k , _))
        ≡⟨ congS (⊎.rec _ _) (finSplit-beta-inl k k<cutoff _) ⟩
          ⊎.rec  
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (inl (k , _))
        ≡⟨⟩
          zs (aut .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inl (k , _)))))
        ≡⟨ congS (zs ∘ aut .fun) (Fin-fst-≡ refl) ⟩
          zs (aut .fun (k , p))  
      ∎)
      (λ cutoff≤k ->
          _
        ≡⟨ sym (transport-filler _ _) ⟩
          ⊎.rec
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (finSplit cutoff (m ∸ cutoff) (k , _))
        ≡⟨ congS (⊎.rec _ _) (finSplit-beta-inr k _ cutoff≤k (<-∸-< k m cutoff p cutoff<)) ⟩
          ⊎.rec
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ aut .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (inr (k ∸ cutoff , _))
        ≡⟨⟩
          zs (aut .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inr (k ∸ cutoff , _)))))
        ≡⟨ congS (zs ∘ aut .fun) (Fin-fst-≡ (+-comm cutoff (k ∸ cutoff) ∙ ≤-∸-+-cancel cutoff≤k)) ⟩
          zs (aut .fun (k , p))  
      ∎)
      (k ≤? cutoff)

  permuteInvariant' : ∀ n tag -> n ≡ tag -- to help termination checker
                  -> (zs : Fin n -> A) (aut : Iso (Fin n) (Fin n))
                  -> f♯ (n , zs ∘ aut .fun) ≡ f♯ (n , zs)

  permuteInvariantOnZero : ∀ n tag -> suc (suc n) ≡ suc tag
                  -> (zs : Fin (suc (suc n)) -> A) (aut : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
                  -> aut .fun fzero ≡ fzero
                  -> f♯ (suc (suc n) , zs ∘ aut .fun) ≡ f♯ (suc (suc n) , zs)
  permuteInvariantOnZero n tag tag≡ zs aut aut-0≡0 =
      f (zs (aut .fun fzero)) 𝔜.⊕ (f♯ (suc n , zs ∘ aut .fun ∘ fsuc))
    ≡⟨ congS (λ z -> f (zs z) 𝔜.⊕ (f♯ (suc n , zs ∘ aut .fun ∘ fsuc))) (Fin-fst-≡ (congS fst aut-0≡0)) ⟩
      f (zs fzero) 𝔜.⊕ (f♯ (suc n , zs ∘ aut .fun ∘ fsuc))
    ≡⟨ congS (λ z -> f (zs fzero) 𝔜.⊕ (f♯ z)) (ΣPathP {x = suc n , zs ∘ aut .fun ∘ fsuc} (refl , toPathP (funExt lemma))) ⟩
      f (zs fzero) 𝔜.⊕ f♯ (suc n , zs ∘ fsuc ∘ punchOutZero aut aut-0≡0 .fun)
    ≡⟨ cong₂ 𝔜._⊕_ (sym (𝔜.unitr _)) (permuteInvariant' (suc n) tag (injSuc tag≡) (zs ∘ fsuc) (punchOutZero aut aut-0≡0)) ⟩
      f♯ (η (zs fzero)) 𝔜.⊕ f♯ (suc n , zs ∘ fsuc)
    ≡⟨ sym (f♯-hom-⊕ (η (zs fzero)) (suc n , zs ∘ fsuc)) ⟩
      f♯ (η (zs fzero) ⊕ (suc n , zs ∘ fsuc))
    ≡⟨ congS f♯ (η+fsuc zs) ⟩
      f♯ (suc (suc n) , zs) ∎
    where
    lemma : _
    lemma w =
        transport (λ _ -> A) (zs (aut .fun (fsuc (transport (λ _ → Fin (suc n)) w))))
      ≡⟨ sym (transport-filler _ _) ⟩
        zs (aut .fun (fsuc (transport (λ _ → Fin (suc n)) w)))
      ≡⟨ congS (λ z -> zs (aut .fun (fsuc z))) (sym (transport-filler _ _)) ⟩
        zs (aut .fun (fsuc w))
      ≡⟨ congS zs (punchOutZero≡fsuc aut aut-0≡0 w) ⟩
        zs (fsuc (punchOutZero aut aut-0≡0 .fun w)) ∎

  permuteInvariant' (suc (suc n)) zero tag≡ zs aut =
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
  permuteInvariant' (suc (suc n)) (suc tag) tag≡ zs aut =
      f♯ (suc (suc n) , zs ∘ aut .fun)
    ≡⟨ sym (swapAutToAut zs aut) ⟩
      f♯ (suc (suc n) , zs ∘ swapAut aut .fun)
    ≡⟨ permuteInvariantOnZero n tag tag≡ zs (swapAut aut) (swapAut0≡0 aut) ⟩
      f♯ (suc (suc n) , zs) ∎

  permuteInvariant : ∀ n (zs : Fin n -> A) (aut : Iso (Fin n) (Fin n)) -> f♯ (n , zs ∘ aut .fun) ≡ f♯ (n , zs)
  permuteInvariant n = permuteInvariant' n n refl

  symm-resp-f♯ : {as bs : Array A} -> SymmAction as bs -> f♯ as ≡ f♯ bs
  symm-resp-f♯ {as = n , g} {bs = m , h} (σ , p) =
      f♯ (n , g)
    ≡⟨ congS (λ z -> f♯ (n , z)) p ⟩
      f♯ (n , h ∘ σ .fun)
    ≡⟨ congS f♯ (ΣPathP (n≡m , toPathP (funExt lemma))) ⟩
      f♯ (m , h ∘ σ .fun ∘ (finIso (sym n≡m)) .fun)
    ≡⟨⟩
      f♯ (m , h ∘ (compIso (finIso (sym n≡m)) σ) .fun)
    ≡⟨ permuteInvariant m h (compIso (finIso (sym n≡m)) σ) ⟩
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

  PermRel : PermRelation arrayDef A
  PermRel = SymmAction , isPermRelPerm

module BagDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

bagFreeDef : ∀ {ℓ} -> BagDef.Free ℓ ℓ 2
bagFreeDef = qFreeMonDef (PermRel _)

Bag : Type ℓ -> Type ℓ
Bag A = BagDef.Free.F bagFreeDef A
