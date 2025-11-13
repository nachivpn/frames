{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

-- Neighborhood frame
module Frame.NFrame {W : Set} {_⊆_ : W → W → Set}
  -- Intuitionistic Frame
  (IF : Preorder W _⊆_)
  (let open Preorder IF)
  -- Neighborhood directory
  (N   : W → Set)
  -- Membership relation that lists worlds (i.e. neighbors)
  -- at an element of the directory (i.e. neighborhood)
  -- v ∈ n means v is in the neighborhood n (of w)
  (_∈_ : (v : W) {w : W} → N w → Set)
  where

open import Function using (const ; flip ; id ; _∘_)

open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)

private
  variable
    w w' w'' u u' v v' : W

-- a predicate satisfied by all elements of a neighborhood
ForAllW : (n : N w) (P : W → Set) → Set
ForAllW n P = ∀ {v} → v ∈ n → P v

-- ForAllW flipped
AllForW : (P : W → Set) (n : N w) → Set
AllForW P n = ForAllW n P

-- a predicate satisfied by all proofs witnessing membership
ForAll∈ : (n : N w) (P : ∀ {v} → v ∈ n → Set) → Set
ForAll∈ n P = ∀ {v} → (p : v ∈ n) → P p

-- a predicate is satisfied by some neighbor
ExistsW : (n : N w) (P : W → Set) → Set
ExistsW n P = ∃ λ w → w ∈ n × P w

-- a predicate is satisfied by some proof witnessing membership of a neighborhood
Exists∈ : (n : N w) (P : ∀ {v} → v ∈ n → Set) → Set
Exists∈ n P = ∃₂ λ v (p : v ∈ n) → P p

-- refinement relation
-- read n ≼ n' as "n' refines n"
_≼_ : N w → N w' → Set
n ≼ n' = ForAllW n' (λ v' → ∃ λ v → v ∈ n × (v ⊆ v'))

≼-refl[_] : (n : N w) → n ≼ n
≼-refl[ n ] {v} p = v , p , ⊆-refl[ v ]

≼-trans : {n : N w} {n' : N w'} {n'' : N w''}
  → n ≼ n' → n' ≼ n'' → n ≼ n''
≼-trans is is' {v''} p'' = let
  (v' , p' , i') = is' p''
  (v , p , i)    = is p'
  in (v , p , ⊆-trans i i')

-- Goldblatt10's refinement condition
record Refinement : Set where

  field

    wkN : w ⊆ w' → N w → N w'

    wkN-refines : (i : w ⊆ w') (n : N w) → n ≼ wkN i n

-- Goldblatt10's localic condition
-- Perhaps shouldn't be "WeakReachability" due to the
-- additional requirement to produce a refined neighborhood
record Localic : Set where

  field

    -- Every neighborhood can be refined to another neighborhood,
    -- s.t. members of the refined neighborhood are reachable via ⊆
    localN : N w → N w

    localN-refines : (n : N w) → (n ≼ localN n)

    localN-reachable : (n : N w) → ForAllW (localN n) (w ⊆_ )

-- Neighborhood generalisation of Rm ⊆ Ri in IML (FairtloughM97)
-- alternatively, states that a neighborhood defines a covering family
record Reachability : Set where

  field

    -- Every neighbor in a neighborhood is reachable via ⊆
    reachable : (n : N w) → ForAllW n (w ⊆_)

  localic : Localic
  localic = record
    { localN           = id
    ; localN-refines   = ≼-refl[_]
    ; localN-reachable = reachable
    }

-- Neighborhood generalisation of "Rm ; Ri⁻¹ is reflexive" (PlotkinS86)
record WeakIdentity : Set where

  field

    --
    idN[_] : ∀ w → N w

    -- 
    idN-bwd-reachable : ForAllW (idN[ w ]) (w ⊆_ )

-- Neighborhood generalisation of "Rm is reflexive"
-- { w } ∈ N w
record Identity : Set where

  field

    -- "identity" neighborhood
    idN[_] : ∀ w → N w

    -- w is the only member of idN
    idN-bwd-member : ForAllW (idN[ w ]) (w ≡_)

  weakIdentity : WeakIdentity
  weakIdentity = record
    { idN[_]            = idN[_]
    ; idN-bwd-reachable = λ {w} {v} v∈P → ≡-subst (_ ⊆_) (idN-bwd-member v∈P) ⊆-refl[ w ]
    }

-- Neighborhood generalisation of Rm² ⊆ Rm ; Ri⁻¹ in IML (PlotkinS86)
record WeakTransitivity : Set where

  field

    --
    transN : (n : N w) → ForAllW n N → N w

    --
    transN-bwd-reachable : (n : N w) (h : ForAllW n N)
      → ForAllW (transN n h) λ v' → Exists∈ n λ u∈n → ExistsW (h u∈n) (_⊆ v')

-- Neighborhood generalisation of "Rm is transitive"
-- If n ∈ N w and for all v ∈ n there exists nᵥ ∈ N v, then Uᵥ nᵥ ∈ N w
record Transitivity : Set where

  field

    -- the neighborhoods of every neighbor (in a given neighborhood n) of w
    -- form a "joint" neighborhood of w
    transN : (n : N w) → ForAllW n N → N w

    -- every world v in a joint neighborhood is the neighbor's neighbor
    -- of some world in the original neighborhood n
    transN-bwd-member : (n : N w) (h : ForAllW n N)
      → ForAllW (transN n h) λ v → Exists∈ n λ u∈n → v ∈ h u∈n

  weakTransitivity : WeakTransitivity
  weakTransitivity = record
    { transN               = transN
    ; transN-bwd-reachable = λ n h {v} v∈J →
      let (u , u∈n , v∈h⟨u∈n⟩) = transN-bwd-member n h v∈J
      in u , u∈n , v , v∈h⟨u∈n⟩ , ⊆-refl[ v ]
    }

-- ∅ ∈ N w
record Empty : Set where

  field
    -- the "empty" neighborhood
    emptyN[_] : ∀ w → N w

    -- no world belongs to the empty neighborhood
    emptyN-bwd-absurd : ForAllW (emptyN[ w ]) λ _ → ⊥

-- N w ≠ ∅
record NonEmpty : Set where

  field
    -- the "unit" neighborhood
    unitN[_] : ∀ w → N w

-- Weakly closed under intersection
record WeaklyClosedUnderInt : Set where

  field

    -- 
    _⊗_ : N w → N w → N w

    --
    ⊗-bwd-reachable : (n1 n2 : N w) → ForAllW (n1 ⊗ n2)
      λ v → ∃₂ λ v1 v2 → v1 ∈ n1 × v1 ⊆ v × v2 ∈ n2 × v2 ⊆ v

-- Closure under insersection
-- n1, n2 ∈ N w implies n1 ∩ n2 ∈ N w
record ClosedUnderInt : Set where

  field

    -- the "intersection neighborhood"
    _⊗_ : N w → N w → N w

    -- a member of n1 ⊗ n2 is a member of both n1 and n2
    ⊗-bwd-reachable : (n1 n2 : N w) → ForAllW (n1 ⊗ n2)
      λ v → v ∈ n1 × v ∈ n2

  weaklyClosedUnderInt : WeaklyClosedUnderInt
  weaklyClosedUnderInt = record
    { _⊗_             = _⊗_
    ; ⊗-bwd-reachable = λ n1 n2 v∈n1⊗n2 →
      let (v∈n1 , v∈n2) = ⊗-bwd-reachable n1 n2 v∈n1⊗n2
      in (-, (-, v∈n1 , ⊆-refl , v∈n2 , ⊆-refl))
    }

-- Closure under union
-- n1, n2 ∈ N w implies n1 ∪ n2 ∈ N w
record ClosedUnderUni : Set where

  field

    -- the "union neighborhood"
    _⊕_ : N w → N w → N w

    -- a member of n1 ⊕ n2 is a member of either n1 or n2
    ⊕-bwd-reachable : (n1 n2 : N w) → ForAllW (n1 ⊕ n2)
      λ v → v ∈ n1 ⊎ v ∈ n2

record Nuclear : Set where
  field
    refinement   : Refinement
    reachability : Reachability
    identity     : Identity
    transitivity : Transitivity

  open Refinement refinement public
  open Reachability reachability public
  open Identity identity public
  open Transitivity transitivity public
