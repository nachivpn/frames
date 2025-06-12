{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF

open import Data.Unit using (⊤)
open import Function using (const)

open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    w w' w'' u u' v v' : W

record KPsh : Set₁ where
  field

    -- type of covers
    -- an element `k : K w` is a cover of w
    K   : W → Set

    -- if w ⊆ w', then for `k : K w` there exists a `K w'`
    wkK : w ⊆ w' → K w → K w'

    -- wkK is functorial
    wkK-pres-refl  : (k : K w) → wkK ⊆-refl[ w ] k ≡ k
    wkK-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (k : K w) → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k)

module Core
  (𝒦 : KPsh)
  (let open KPsh 𝒦)
  -- `v ∈ (k : K w)` means v is in the cover k
  (_∈_ : (v : W) {w : W} → K w → Set)
  where

  -- a predicate is satisfied by all elements of a cover
  ForAllW : (k : K w) (P : W → Set) → Set
  ForAllW k P = ∀ {v} → v ∈ k → P v

  -- a predicate is satisfied by all proofs witnessing membership of a cover
  ForAll∈ : (k : K w) (P : ∀ {v} → v ∈ k → Set) → Set
  ForAll∈ k P = ∀ {v} → (p : v ∈ k) → P p

  -- inclusion of covers
  _⊆k_ : K w → K w' → Set
  k ⊆k k' = ForAllW k' (λ v' → ∃ λ v → v ∈ k × (v ⊆ v'))

  -- equality on cover inclusion proofs
  _≋_ : {k : K w} {k' : K w'} → k ⊆k k' → k ⊆k k' → Set
  _≋_  {w} {w'} {k} {k'} is is' = ForAll∈ k' λ p → is p ≡ is' p

  --
  ⊆k-refl[_] : (k : K w) → k ⊆k k
  ⊆k-refl[ k ] {v} p = v , p , ⊆-refl[ v ]

  --
  ⊆k-trans : {k : K w} {k' : K w'} {k'' : K w''}
    → k ⊆k k' → k' ⊆k k'' → k ⊆k k''
  ⊆k-trans is is' {v''} p'' = let
    (v' , p' , i') = is' p''
    (v , p , i)    = is p'
    in (v , p , ⊆-trans i i')

  -- TODO: show ⊆k-refl is the left and right unit of ⊆k-trans?

  -- specialized and type-casted ⊆k-refl
  ⊆k-refl[_]' : (k : K w) → k ⊆k wkK ⊆-refl k
  ⊆k-refl[ k ]' {v} rewrite wkK-pres-refl k = ⊆k-refl[ k ]

  -- specialized and type-casted ⊆k-trans
  ⊆k-trans' : {i : w ⊆ w'} {i' : w' ⊆ w''} (k : K w)
    → k ⊆k wkK i k
    → wkK i k ⊆k wkK i' (wkK i k)
    → k ⊆k wkK (⊆-trans i i') k
  ⊆k-trans' {i = i} {i'} k x y rewrite wkK-pres-trans i i' k = ⊆k-trans x y

  record CFrame : Set₁ where

    field

      factor : (i : w ⊆ w') (k : K w) → k ⊆k wkK i k

      factor-pres-refl : (k : K w)
        → factor ⊆-refl k ≋ ⊆k-refl[ k ]'

      factor-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (k : K w)
        → factor (⊆-trans i i') k ≋ ⊆k-trans' k (factor i k) (factor i' (wkK i k))

    factorW : (o : w ⊆ w') (k : K w) → ∀ {v'} → (p : v' ∈ wkK o k) → W
    factorW o k p = factor o k p .fst

    factor∈ : (o : w ⊆ w') (k : K w) → ∀ {v'} → (p : v' ∈ wkK o k) → factor o k p .fst ∈ k
    factor∈ o k p = factor o k p .snd .fst

    factor⊆ : (o : w ⊆ w') (k : K w) → ∀ {v'} → (p : v' ∈ wkK o k) → factor o k p .fst ⊆ v'
    factor⊆ o k p = factor o k p .snd .snd

  module _ (CF : CFrame) where

    open CFrame CF

    record Coverage : Set₁ where
      field
        family : (k : K w) → ForAllW k (w ⊆_)

    -- Identity condition
    record Pointed : Set where

      field
        pointK[_] : ∀ w → K w
        point∈    : ForAllW (pointK[ w ]) λ v → w ≡ v

    -- Transitivity condition
    record Joinable : Set₁ where

      field
        joinK : (k : K w) → ForAllW k K → K w
        join∈ : (k : K w) (f : ForAllW k K) → ForAllW (joinK k f) λ v' → ∃₂ λ v (p : v ∈ k) → v' ∈ f p

    -- Note: Speculative!
    record CoPointed : Set where
      field
        copoint∈ : (k : K w) → w ∈ k

    -- Note: Speculative!
    record CoJoinable : Set₁ where

      field
        cojoinK : (k : K w) → v ∈ k → K v
        cojoin∈ : (k : K w) (p : v ∈ k) → ForAllW (cojoinK k p) (_∈ k)
