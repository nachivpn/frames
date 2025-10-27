{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.NFrame {W : Set} {_⊆_ : W → W → Set} (IF : Preorder W _⊆_) where

open Preorder IF

open import Function using (const ; flip ; id ; _∘_)

open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Empty using (⊥)

private
  variable
    w w' w'' u u' v v' : W

module Core
  -- Neighborhood function, which assigns a neighborhood to a world
  -- Intuition: think of K having the type W → 𝒫 (𝒫 W)
  (K   : W → Set)
  -- Membership relation: v ∈ k means v is in the neighborhood k (of w)
  -- Intuition: set membership
  (_∈_ : (v : W) {w : W} → K w → Set)
  where

  -- a predicate satisfied by all elements of a neighborhood
  ForAllW : (k : K w) (P : W → Set) → Set
  ForAllW k P = ∀ {v} → v ∈ k → P v

  -- ForAllW flipped
  AllForW : (P : W → Set) (k : K w) → Set
  AllForW P k = ForAllW k P

  -- a predicate satisfied by all proofs witnessing membership
  ForAll∈ : (k : K w) (P : ∀ {v} → v ∈ k → Set) → Set
  ForAll∈ k P = ∀ {v} → (p : v ∈ k) → P p

  -- a predicate is satisfied by some neighbor
  ExistsW : (k : K w) (P : W → Set) → Set
  ExistsW k P = ∃ λ w → w ∈ k × P w

  -- a predicate is satisfied by some proof witnessing membership of a neighborhood
  Exists∈ : (k : K w) (P : ∀ {v} → v ∈ k → Set) → Set
  Exists∈ k P = ∃₂ λ v (p : v ∈ k) → P p

  -- ordering of neighborhoods
  _⊆k_ : K w → K w' → Set
  k ⊆k k' = ForAllW k' (λ v' → ∃ λ v → v ∈ k × (v ⊆ v'))

  ⊆k-refl[_] : (k : K w) → k ⊆k k
  ⊆k-refl[ k ] {v} p = v , p , ⊆-refl[ v ]

  ⊆k-trans : {k : K w} {k' : K w'} {k'' : K w''}
    → k ⊆k k' → k' ⊆k k'' → k ⊆k k''
  ⊆k-trans is is' {v''} p'' = let
    (v' , p' , i') = is' p''
    (v , p , i)    = is p'
    in (v , p , ⊆-trans i i')

  record NFrame : Set₁ where

    field

      wkK        : w ⊆ w' → K w → K w'

      wkK-resp-⊆ : (i : w ⊆ w') (k : K w) → k ⊆k wkK i k

  module _ (CF : NFrame) where

    open NFrame CF

    record Reachable : Set₁ where

      field

        -- "reachability" condition
        -- Every neighbor in a neighborhood is reachable via ⊆
        reachable : (k : K w) → ForAllW k (w ⊆_)

    record Pointed : Set where

      field

        -- a "pointed" neighborhood
        pointK[_] : ∀ w → K w

        -- every neighbor in pointK is an intuitionistic future of w reachable through ⊆
        pointK-bwd-reachable : ForAllW (pointK[ w ]) (w ⊆_ )

    record StrictlyPointed : Set where

      field

        -- a "pointed" neighborhood
        pointK[_] : ∀ w → K w

        -- w is the only member of pointK
        pointK-bwd-member : ForAllW (pointK[ w ]) (w ≡_)

      pointed : Pointed
      pointed = record
        { pointK[_]        = pointK[_]
        ; pointK-bwd-reachable = λ {w} {v} v∈P → ≡-subst (_ ⊆_) (pointK-bwd-member v∈P) ⊆-refl[ w ]
        }

    record Joinable : Set₁ where

      field

        -- the neighborhoods of every neighbor (in a given neighborhood k) of w
        -- form a "joint" neighborhood of w
        joinK : (k : K w) → ForAllW k K → K w

        -- every world v' in a joint neighborhood is the neighbor's neighbor's past
        -- of some world in the original neighborhood k
        joinK-bwd-reachable : (k : K w) (h : ForAllW k K)
          → ForAllW (joinK k h) λ v' → Exists∈ k λ u∈k → ExistsW (h u∈k) (_⊆ v')

    record StrictlyJoinable : Set₁ where

      field

        -- the neighborhoods of every neighbor (in a given neighborhood k) of w
        -- form a "joint" neighborhood of w
        joinK : (k : K w) → ForAllW k K → K w

        -- every world v in a joint neighborhood is the neighbor's neighbor
        -- of some world in the original neighborhood k
        joinK-bwd-member : (k : K w) (h : ForAllW k K)
          → ForAllW (joinK k h) λ v → Exists∈ k λ u∈k → v ∈ h u∈k

      joinable : Joinable
      joinable = record
        { joinK     = joinK
        ; joinK-bwd-reachable = λ k h {v} v∈J →
          let (u , u∈k , v∈h⟨u∈k⟩) = joinK-bwd-member k h v∈J
          in u , u∈k , v , v∈h⟨u∈k⟩ , ⊆-refl[ v ]
        }

    -- ∅ ∈ K w
    record Empty : Set₁ where

      field
        emptyK[_] : ∀ w → K w
        emptyK-bwd-absurd : ForAllW (emptyK[ w ]) λ _ → ⊥

    -- ∅ ∉ K w
    record Unital : Set₁ where

      field
        unitK[_] : ∀ w → K w

    -- k1, k2 ∈ K w implies k1 ∩ k2 ∈ K w
    record Magma : Set₁ where

      field

        _⊗_ : K w → K w → K w

        ⊗-bwd-reachable : (k1 k2 : K w) → ForAllW (k1 ⊗ k2)
          λ v → ∃₂ λ v1 v2 → v1 ∈ k1 × v1 ⊆ v × v2 ∈ k2 × v2 ⊆ v
