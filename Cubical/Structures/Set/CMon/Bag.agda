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
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as EQ
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

symmActionLength≡ : {n m : ℕ} -> Fin n ≃ Fin m -> n ≡ m
symmActionLength≡ {n = n} {m = m} act with discreteℕ n m
... | yes p = p
... | no ¬p = ⊥.rec (¬p (Fin-inj n m (ua act)))

equivFun∘invEq : ∀ {n m} (act : Fin n ≃ Fin m) w -> (equivFun act ∘ invEq act) w ≡ w
equivFun∘invEq act w = invEq≡→equivFun≡ act refl

invEq∘equivFun : ∀ {n m} (act : Fin n ≃ Fin m) w -> (invEq act ∘ equivFun act) w ≡ w
invEq∘equivFun act w = equivFun∘invEq (invEquiv act) w

-- TODO: Try to prove this to generalize all the proofs under
-- ℕ≡→symm : ∀ {A : Type ℓ} {k} (lhs : FinTree M.CMonFinSig k) (rhs : FinTree M.CMonFinSig k)
--         -> ((fℕ : Fin k -> ℕ) -> sharp M.CMonSig M.ℕ-CMonStr fℕ lhs ≡ sharp M.CMonSig M.ℕ-CMonStr fℕ rhs)
--         -> ((fA : Fin k -> Array A) -> SymmAction (sharp M.MonSig (array-str A) fA lhs) (sharp M.MonSig (array-str A) fA rhs))
-- ℕ≡→symm {A = A} lhs rhs eqn fA =
--   ℕ≡→Fin̄≅ (Array→ℕ lhs ∙ eqn (fst ∘ fA) ∙ sym (Array→ℕ rhs)) , funExt lemma
--   where
--   Array→ℕ : ∀ tr -> fst (sharp M.MonSig (array-str A) fA tr) ≡ sharp M.CMonSig M.ℕ-CMonStr (fst ∘ fA) tr
--   Array→ℕ (leaf x) = refl
--   Array→ℕ (node x) = {! λ i → ? !}
-- 
--   lemma : _
--   lemma (w , p) = {!   !}

symm-append : ∀ {xs ys} -> SymmAction xs ys -> {zs : Array A} -> SymmAction (xs ⊕ zs) (ys ⊕ zs)
symm-append {xs = (n , xs)} {ys = (m , ys)} (act , eqn) {zs = (o , zs)} =
  isoToEquiv (iso (append act) (append (invEquiv act)) (to∘from act) (to∘from (invEquiv act))) , funExt symActEq
  where
  append : ∀ {a b} -> Fin a ≃ Fin b -> Fin (a + o) -> Fin (b + o)
  append {a = a} {b = b} f = combine a o (finCombine b o ∘ inl ∘ equivFun f) (finCombine b o ∘ inr)

  to∘from : ∀ {a b} (f : Fin a ≃ Fin b) x -> append f (append (invEquiv f) x) ≡ x
  to∘from {a = a} {b = b} f (w , p) with w ≤? b
  to∘from {a = a} {b = b} f (w , p) | inl q with fst (invEq f (w , q)) ≤? a
  to∘from {a = a} {b = b} f (w , p) | inl q | inl r =
    ΣPathP (lemma , toPathP (isProp≤ _ p))
    where
    lemma : _
    lemma =
      fst (fst f (fst (snd f .equiv-proof (w , q) .fst .fst) , r)) ≡⟨ cong (λ z -> fst (fst f z)) (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
      fst (fst f (snd f .equiv-proof (w , q) .fst .fst)) ≡⟨ cong fst (equivFun∘invEq f (w , q)) ⟩
      w ∎
  to∘from {a = a} {b = b} f (w , p) | inl q | inr r =
    ⊥.rec (<-asym (snd (invEq f (w , q))) r)
  to∘from {a = a} {b = b} f (w , p) | inr q with (a + (w ∸ b)) ≤? a
  to∘from {a = a} {b = b} f (w , p) | inr q | inl r =
    ⊥.rec (¬m+n<m r)
  to∘from {a = a} {b = b} f (w , p) | inr q | inr r =
    ΣPathP (lemma , toPathP (isProp≤ _ p))
    where
    lemma : b + (a + (w ∸ b) ∸ a) ≡ w
    lemma =
      b + (a + (w ∸ b) ∸ a) ≡⟨ cong (b +_) (∸+ (w ∸ b) a) ⟩
      b + (w ∸ b) ≡⟨ +-comm b (w ∸ b) ⟩
      (w ∸ b) + b ≡⟨ ≤-∸-+-cancel q ⟩
      w ∎

  symActEq : (x : Fin (fst ((n , xs) ⊕ (o , zs)))) -> snd ((n , xs) ⊕ (o , zs)) x ≡ snd ((m , ys) ⊕ (o , zs)) (append act x)
  symActEq (w , p) with w ≤? n
  symActEq (w , p) | inl q with fst (equivFun act (w , q)) ≤? m
  symActEq (w , p) | inl q | inl r =
    xs (w , q) ≡⟨ cong (λ f -> f (w , q)) eqn ⟩
    ys (fst act (w , q)) ≡⟨ cong ys (Σ≡Prop (λ _ -> isProp≤) refl) ⟩
    ys (fst (fst act (w , q)) , r) ∎
  symActEq (w , p) | inl q | inr r = ⊥.rec (<-asym (snd (equivFun act (w , q))) r)
  symActEq (w , p) | inr q with (m + (w ∸ n)) ≤? m
  symActEq (w , p) | inr q | inl r = ⊥.rec (¬m+n<m r)
  symActEq (w , p) | inr q | inr r = cong zs (Σ≡Prop (λ _ -> isProp≤) (sym (∸+ (w ∸ n) m)))

symm-prepend : ∀ xs {ys zs : Array A} -> SymmAction ys zs -> SymmAction (xs ⊕ ys) (xs ⊕ zs)
symm-prepend (n , xs) {ys = (m , ys)} {zs = (o , zs)} (act , eqn) =
  isoToEquiv (iso (prepend act) (prepend (invEquiv act)) (to∘from act) (to∘from (invEquiv act))) , funExt symActEq
  where
  prepend : ∀ {a b} -> Fin a ≃ Fin b -> Fin (n + a) -> Fin (n + b)
  prepend {a = a} {b = b} f = combine n a (finCombine n b ∘ inl) (finCombine n b ∘ inr ∘ equivFun f)

  to∘from : ∀ {a b} (f : Fin a ≃ Fin b) x -> prepend f (prepend (invEquiv f) x) ≡ x
  to∘from {a = a} {b = b} f (w , p) with w ≤? n
  to∘from {a = a} {b = b} f (w , p) | inl q with w ≤? n
  to∘from {a = a} {b = b} f (w , p) | inl q | inl r = Σ≡Prop (λ _ -> isProp≤) refl
  to∘from {a = a} {b = b} f (w , p) | inl q | inr r = ⊥.rec (<-asym q r)
  to∘from {a = a} {b = b} f (w , p) | inr q with (n + (invEq f (w ∸ n , ∸-<-lemma n b w p q)) .fst) ≤? n
  to∘from {a = a} {b = b} f (w , p) | inr q | inl r = ⊥.rec (¬m+n<m r)
  to∘from {a = a} {b = b} f (w , p) | inr q | inr r =
    Σ≡Prop (λ _ -> isProp≤) lemma
    where
    lemma : _
    lemma =
        n + fst (equivFun f (n + fst (invEq f (w ∸ n , ∸-<-lemma n b w p q)) ∸ n , ∸-<-lemma n a _ _ r))
      ≡⟨ cong (λ z -> n + fst (equivFun f z)) (Σ≡Prop (λ _ -> isProp≤) (∸+ _ n)) ⟩
        n + fst (equivFun f (invEq f (w ∸ n , ∸-<-lemma n b w p q)))
      ≡⟨ cong (λ z -> n + fst z) (equivFun∘invEq f (w ∸ n , ∸-<-lemma n b w p q)) ⟩
        n + (w ∸ n)
      ≡⟨ +-comm n _ ⟩
        (w ∸ n) + n
      ≡⟨ ≤-∸-+-cancel q ⟩
        w ∎

  symActEq : _
  symActEq (w , p) with w ≤? n
  symActEq (w , p) | inl q with w ≤? n
  symActEq (w , p) | inl q | inl r = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)
  symActEq (w , p) | inl q | inr r = ⊥.rec (<-asym q r)
  symActEq (w , p) | inr q with (n + fst (fst act (w ∸ n , ∸-<-lemma n m w p q))) ≤? n
  symActEq (w , p) | inr q | inl r = ⊥.rec (¬m+n<m r)
  symActEq (w , p) | inr q | inr r =
      ys (w ∸ n , ∸-<-lemma n m w p q)
    ≡⟨ cong (λ f -> f (w ∸ n , ∸-<-lemma n m w p q)) eqn ⟩
      zs (act .fst (w ∸ n , ∸-<-lemma n m w p q))
    ≡⟨ cong zs (Σ≡Prop (λ _ -> isProp≤) (sym (∸+ _ n))) ⟩
      zs (n + fst (act .fst (w ∸ n , ∸-<-lemma n m w p q)) ∸ n , _) ∎

⊕-unitlₚ : (as : Array A) -> SymmAction (e ⊕ as) as
⊕-unitlₚ (n , as) = ℕ≡→Fin̄≅ refl , funExt lemma
  where
  lemma : (x : Fin (fst (e ⊕ (n , as)))) -> snd (e ⊕ (n , as)) x ≡ as (ℕ≡→Fin̄≅ (λ _ → n) .fst x)
  lemma (m , p) with m ≤? 0
  lemma (m , p) | inl q = ⊥.rec (¬-<-zero q)
  lemma (m , p) | inr q = cong as (transport-filler refl (m , p))

⊕-unitrₚ : (as : Array A) -> SymmAction (as ⊕ e) as
⊕-unitrₚ (n , as) = ℕ≡→Fin̄≅ (+-zero n) , funExt lemma
  where
  lemma : (x : Fin (fst ((n , as) ⊕ e))) -> snd ((n , as) ⊕ e) x ≡ as (ℕ≡→Fin̄≅ (+-zero n) .fst x)
  lemma (m , p) with m ≤? n
  lemma (m , p) | inl q =
    cong as (sym (fromPathP λ i → m , lemma-α i))
    where
    lemma-α : PathP (λ i -> Σ ℕ (λ k₁ → k₁ + suc m ≡ +-zero n i)) p q
    lemma-α = toPathP (isProp≤ _ q)
  lemma (m , p) | inr q = ⊥.rec (<-asym p (subst (_≤ m) (sym (+-zero n)) q))

⊕-assocrₚ : (as bs cs : Array A) -> SymmAction ((as ⊕ bs) ⊕ cs) (as ⊕ (bs ⊕ cs))
⊕-assocrₚ (n , as) (m , bs) (o , cs) =
  ℕ≡→Fin̄≅ (sym (+-assoc n m o)) , funExt lemma
  where
  lemma : _
  lemma (w , p) with w ≤? (n + m)
  lemma (w , p) | inl q with w ≤? n
  lemma (w , p) | inl q | inl r = refl
  lemma (w , p) | inl q | inr r with (w ∸ n) ≤? m
  lemma (w , p) | inl q | inr r | inl s = cong bs (Σ≡Prop (λ _ -> isProp≤) refl)
  lemma (w , p) | inl q | inr r | inr s = ⊥.rec (<-asym q (subst (n + m ≤_) (+-comm n (w ∸ n) ∙ ≤-∸-+-cancel r) (≤-k+ s)))
  lemma (w , p) | inr q with w ≤? n
  lemma (w , p) | inr q | inl r = ⊥.rec (¬m+n<m (≤<-trans q r))
  lemma (w , p) | inr q | inr r with (w ∸ n) ≤? m
  lemma (w , p) | inr q | inr r | inl s = ⊥.rec (<-asym s (subst (_≤ w ∸ n) (∸+ m n) (≤-∸-≤ _ _ n q)))
  lemma (w , p) | inr q | inr r | inr s = cong cs (Σ≡Prop (λ _ -> isProp≤) (sym (∸-+-assoc w n _)))

⊕-commₚ : (xs ys : Array A) -> SymmAction (xs ⊕ ys) (ys ⊕ xs)
⊕-commₚ (n , xs) (m , ys) =
  isoToEquiv (iso (comm n m) (comm m n) (comm∘comm n m) (comm∘comm m n)) , funExt symActEq
  where
  comm : ∀ a b -> Fin (a + b) -> Fin (b + a)
  comm a b = combine a b (finCombine b a ∘ inr) (finCombine b a ∘ inl)

  comm∘comm : ∀ a b x -> comm a b (comm b a x) ≡ x
  comm∘comm a b (w , p) with w ≤? b
  comm∘comm a b (w , p) | inl q with (a + w) ≤? a
  comm∘comm a b (w , p) | inl q | inl r = ⊥.rec (¬m+n<m r)
  comm∘comm a b (w , p) | inl q | inr r = Σ≡Prop (λ _ -> isProp≤) (∸+ w a)
  comm∘comm a b (w , p) | inr q with (w ∸ b) ≤? a
  comm∘comm a b (w , p) | inr q | inl r = Σ≡Prop (λ _ → isProp≤) (+-comm b (w ∸ b) ∙ ≤-∸-+-cancel q)
  comm∘comm a b (w , p) | inr q | inr r = ⊥.rec (<-asym (subst2 _≤_ (sym (≤-∸-suc q)) (∸+ a b) (≤-∸-≤ _ _ b p)) r)

  symActEq : _
  symActEq (w , p) with w ≤? n
  symActEq (w , p) | inl q with (m + w) ≤? m
  symActEq (w , p) | inl q | inl r = ⊥.rec (¬m+n<m r)
  symActEq (w , p) | inl q | inr r = cong xs (Σ≡Prop (λ _ → isProp≤) (sym (∸+ w m)))
  symActEq (w , p) | inr q with (w ∸ n) ≤? m
  symActEq (w , p) | inr q | inl r = cong ys (Σ≡Prop (λ _ → isProp≤) refl)
  symActEq (w , p) | inr q | inr r = ⊥.rec (<-asym (subst2 _≤_ (sym (≤-∸-suc q)) (∸+ m n) (≤-∸-≤ _ _ n p)) r)

cons : ∀ {n} -> A -> (Fin n -> A) -> (Fin (suc n) -> A)
cons x xs (zero , p) = x
cons x xs (suc n , p) = xs (n , pred-≤-pred p)

uncons : ∀ {n} -> (Fin (suc n) -> A) -> A × (Fin n -> A)
uncons xs = xs fzero , xs ∘ fsuc

cons∘uncons : ∀ {n} -> (xs : Fin (suc n) -> A) (x : Fin (suc n)) -> cons (xs fzero) (xs ∘ fsuc) x ≡ xs x
cons∘uncons xs (zero , p) = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)
cons∘uncons xs (suc n , p) = cong xs (Σ≡Prop (λ _ -> isProp≤) refl)

uncons∘cons : ∀ {n} -> (x : A) -> (xs : Fin (suc n) -> A) -> uncons (cons x xs) ≡ (x , xs)
uncons∘cons x xs = cong (x ,_) (funExt λ _ -> cong xs (Σ≡Prop (λ _ -> isProp≤) refl))

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f-hom : structHom (array-str A) 𝔜) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f : Array A -> 𝔜 .car
  f = f-hom .fst

  id-aut : ∀ {n m} -> n ≡ m -> Fin n ≃ Fin m
  id-aut p = subst Fin p , record
    { equiv-proof = λ y -> (subst Fin (sym p) y , substSubst⁻ Fin p y) , λ (z , q) -> Σ≡Prop (λ _ -> isSetFin _ _) (lemma y z q)
    }
    where
    lemma : ∀ y z q -> subst Fin (λ i → p (~ i)) y ≡ z
    lemma y z q =
      subst Fin (λ i → p (~ i)) y ≡⟨ cong (subst Fin (λ i → p (~ i))) (sym q) ⟩
      subst Fin (λ i → p (~ i)) (subst Fin p z) ≡⟨ subst⁻Subst Fin p z ⟩
      z ∎

  -- id-aut≡ : ∀ {n m} (p : n ≡ m) (w : Fin n) -> (equivFun (id-aut p) w) .fst ≡ w .fst
  -- id-aut≡ p w = refl

  permuteArray : ∀ n (zs : Fin n -> A) (act : LehmerCode n) -> Array A
  permuteArray .zero zs [] = 0 , ⊥.rec ∘ ¬Fin0
  permuteArray .(suc _) zs (p ∷ ps) = η (zs p) ⊕ permuteArray _ (zs ∘ fsuc) ps

  -- permuteInvariant : ∀ n (zs : Fin n -> A) (act : LehmerCode n) -> f (n , zs) ≡ f (permuteArray n zs act)
  -- permuteInvariant .zero zs [] = cong f (ΣPathP (refl , funExt (⊥.rec ∘ ¬Fin0)))
  -- permuteInvariant .(suc _) zs (p ∷ ps) =
  --   {!   !}

  -- compLehmer≡ : ∀ n (zs : Fin n -> A) (act : Fin n ≃ Fin n) ->
  --                 zs ∘ equivFun act ≡ compLehmer n zs (equivFun lehmerEquiv act)
  -- compLehmer≡ zero zs act = funExt (⊥.rec ∘ ¬Fin0)
  -- compLehmer≡ (suc n) zs act = λ i x -> lemma x (~ i)
  --   where
  --   aut-tail : LehmerCode n
  --   aut-tail = snd (invEq lehmerSucEquiv (equivFun lehmerEquiv act))

  --   lemma-α : (x : Fin n) -> fsuc (equivFun (decode aut-tail) x) ≡ equivFun act (fsuc x)
  --   lemma-α = {!   !}

  --   lemma : (x : Fin (suc n)) -> cons _ _ x ≡ (zs ∘ equivFun act) x
  --   lemma x =
  --       cons ((zs ∘ equivFun act) fzero) _ x
  --     ≡⟨ cong (λ z -> cons ((zs ∘ equivFun act) fzero) z x) ((sym (compLehmer≡ n (zs ∘ fsuc) _))) ⟩
  --      cons ((zs ∘ equivFun act) fzero) (zs ∘ fsuc ∘ _) x
  --     ≡⟨ cong (λ z -> cons ((zs ∘ equivFun act) fzero) (zs ∘ z) x) (funExt lemma-α) ⟩
  --       cons ((zs ∘ equivFun act) fzero) (zs ∘ equivFun act ∘ fsuc) x
  --     ≡⟨ cons∘uncons (zs ∘ equivFun act) x ⟩
  --       (zs ∘ equivFun act) x ∎

  compose-equiv : ∀ {A B C : Type ℓ} -> A ≃ B -> B ≃ C -> A ≃ C
  compose-equiv p q = equivFun univalence (ua p ∙ ua q)

  compose-equiv≡ : ∀ {A B C : Type ℓ} (p : A ≃ B) (q : B ≃ C) (x : A)
                 -> equivFun (compose-equiv p q) x ≡ equivFun q (equivFun p x)
  compose-equiv≡ {A = A} {B = B} {C = C} p q x =
    _ ≡⟨ sym (transport-filler _ _) ⟩
    fst q (transp (λ i → B) i0 (fst p (transp (λ i → A) i0 x))) ≡⟨ cong (fst q) (sym (transport-filler _ _)) ⟩
    fst q (fst p (transp (λ i → A) i0 x)) ≡⟨ cong (fst q ∘ fst p) (sym (transport-filler _ _)) ⟩
    fst q (fst p x) ∎

  -- f-≅ₚ : ∀ {xs zs} -> SymmAction xs zs -> f xs ≡ f zs
  -- f-≅ₚ {xs = n , xs} {zs = m , zs} (act , eqn) =
  --     f (n , xs)
  --   ≡⟨ cong (λ z -> f (n , z)) eqn ⟩
  --     f (n , zs ∘ equivFun act)
  --   ≡⟨ cong f (ΣPathP (n≡m , toPathP (funExt (λ _ -> sym (transport-filler _ _))))) ⟩
  --     f (m , zs ∘ (equivFun act ∘ equivFun (id-aut (sym n≡m))))
  --   ≡⟨ cong (λ z -> f (m , zs ∘ z)) (λ i x -> compose-equiv≡ (id-aut (sym n≡m)) act x (~ i)) ⟩
  --     f (m , zs ∘ equivFun (compose-equiv (id-aut (sym n≡m)) act))
  --   ≡⟨ cong f {!   !} ⟩
  --     f (permuteArray m zs (equivFun lehmerEquiv (compose-equiv (id-aut (sym n≡m)) act)))
  --   ≡⟨ {!   !} ⟩
  --     f (m , zs) ∎
  --   where
  --   n≡m : n ≡ m
  --   n≡m = symmActionLength≡ act
    
{-
       (snd
        (Σ-cong-equiv-snd (Cubical.Data.Fin.LehmerCode.ii n) .fst
         (equivFun act fzero , Cubical.Data.Fin.LehmerCode.equivIn n act)))
-}
    