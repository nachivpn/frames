{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

-- Neighborhood library
module Neighborhood.Lib {W : Set} {_⊑_ : W → W → Set}
  -- Intuitionistic Frame
  (IF : Preorder W _⊑_)
  (let open Preorder IF)
  -- Neighborhood directory
  (N   : W → Set)
  -- Membership relation that lists worlds (i.e. neighbors)
  -- at an element of the directory (i.e. neighborhood)
  -- v ∈ n means v is in the neighborhood n (of w)
  (_∈_ : W → {w : W} → N w → Set)
  where

open import Function using (const ; flip ; id ; _∘_)

open import Relation.Binary using (IsEquivalence)
open import Relation.Unary
  using (_∩_ ; _∪_ ; ∅ ; _≐_ ; _≬_ ; ⋃ ; _⊆_)
  renaming (Universal to Forall ; Satisfiable to Exists) public
open import Relation.Unary.Properties
  renaming (⊆-refl to ⊆ₗ-refl ; ⊆-trans to ⊆ₗ-trans) public

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_ ; curry ; uncurry)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)

private
  variable
    w w' w'' u u' v v' : W

-- proof-relevant "subsets" of W
Sub : Set₁
Sub = W → Set

-- set identifying members in a neighborhood
∣_∣ : N w → Sub
∣ n ∣ = λ v → v ∈ n

-- singleton set
⟨_⟩ : W → Sub
⟨ x ⟩ = x ≡_

-- all worlds that refine (i.e. above) w
↑_ : W → Sub
↑ w = w ⊑_

-- all  worlds that refine some member of X
⇑_ : Sub → Sub
⇑ X  = λ w → ∃ λ x → X x × (x ⊑ w)

-- all worlds refined by w
↓_ : W → Sub
↓ w = _⊑ w

⊆-trans : {X Y Z : Sub} → X ⊆ Y → Y ⊆ Z → X ⊆ Z
⊆-trans {Y = Y} f g = ⊆ₗ-trans {A = W} {j = Y} f g

-- "big union"
⨆ : (X : Sub) (X[_] : ∀ {w} → X w → Sub) → Sub
⨆ X X[_] = ⋃ (Exists X) (uncurry λ _ → X[_])

-- a predicate satisfied by all elements of a neighborhood
ForAllW : (n : N w) (X : Sub) → Set
ForAllW n X = ∣ n ∣ ⊆ X

-- ForAllW flipped
AllForW : (X : Sub) (n : N w) → Set
AllForW X n = ForAllW n X

-- a predicate satisfied by all proofs witnessing membership
ForAll∈ : (n : N w) (P : ∀ {v} → v ∈ n → Set) → Set
ForAll∈ n P = ∀ {v} → (p : v ∈ n) → P p

-- a predicate is satisfied by some neighbor
ExistsW : (n : N w) (P : W → Set) → Set
ExistsW n P = ∣ n ∣ ≬ P

-- a predicate is satisfied by some proof witnessing membership of a neighborhood
Exists∈ : (n : N w) (P : ∀ {v} → v ∈ n → Set) → Set
Exists∈ n P = ∃₂ λ v (p : v ∈ n) → P p

--
-- Refinement relation
--

-- read X ≼ Y as "X is refined by Y" or "Y refines X"
_≼_ : Sub → Sub → Set
X ≼ Y = Y ⊆ (⇑ X)

_≽_ : Sub → Sub → Set
Y ≽ X = X ≼ Y

≼-refl[_] : (X : Sub) → X ≼ X
≼-refl[ n ] {v} p = v , p , ⊑-refl[ v ]

≼-trans : {X Y Z : Sub} → X ≼ Y → Y ≼ Z → X ≼ Z
≼-trans is is' {v''} p'' = let
  (v' , p' , i') = is' p''
  (v , p , i)    = is p'
  in (v , p , ⊑-trans i i')

--
-- Note on use of the refinement relation:
-- For a given X : Sub and w : W,
-- to say w refines X, we prefer to write
-- X ⊑ (↑ w) instead of X ≽｛ w  ｝
-- to avoid dealing with identity proofs induced
-- by singleton sets (c.f. defn. of ｛_｝)
--

-- Goldblatt10's refinement condition
record Refinement : Set where
  field
    wkN     : w ⊑ w' → N w → N w'
    wkN-ref : (i : w ⊑ w') (n : N w) → ∣ n ∣ ≼ ∣ wkN i n ∣

-- Goldblatt10's localic condition
record Localic : Set where
  field
    localN     : N w → N w
    -- Every neighborhood of w can be refined to another neighborhood that also refines w
    localN-ref : (n : N w) → ∣ n ∣ ≼ ∣ localN n ∣ × ∣ localN n ∣ ⊆ (↑ w)

  -- Perhaps shouldn't be "WeakInclusion" due to the
  -- additional requirement to produce a refined neighborhood

-- Neighborhood generalisation of Rm ⊑ Ri in IML (FairtloughM97)
-- alternatively, states that a neighborhood defines a covering family
record Inclusion : Set where
  field
    -- Every neighborhood of w refines w
    N-ref : (n : N w) → ∣ n ∣ ⊆ (↑ w)

  localic : Localic
  localic = record
    { localN     = id
    ; localN-ref = λ n → ≼-refl[ ∣ n ∣ ] , N-ref n
    }

-- Neighborhood generalisation of "Rm ; Ri⁻¹ is reflexive" (PlotkinS86)
record WeakIdentity : Set where
  field
    idN[_]  : ∀ w → N w
    idN-ref :  ∣ idN[ w ] ∣ ⊆ (↑ w)

-- Neighborhood generalisation of "Rm is reflexive"
record Identity : Set where
  field
    idN[_]  : ∀ w → N w
    idN-sub : ∣ idN[ w ] ∣ ⊆ ⟨ w ⟩

  weakIdentity : WeakIdentity
  weakIdentity = record
    { idN[_]  = idN[_]
    ; idN-ref = λ {w} {v} v∈P → ≡-subst (_ ⊑_) (idN-sub v∈P) ⊑-refl[ w ]
    }

record HyperIdentity : Set where
  field
    idN[_]  : ∀ w → N w
    idN-equ : ∣ idN[ w ] ∣ ≐ ⟨ w ⟩

  identity : Identity
  identity = record
    { idN[_]  = idN[_]
    ; idN-sub = λ v∈IdN → idN-equ .fst v∈IdN
    }

-- Neighborhood generalisation of Rm² ⊑ Rm ; Ri⁻¹ in IML (PlotkinS86)
record WeakTransitivity : Set where
  field
    transN     : (n : N w) → ForAllW n N → N w
    transN-ref : (n : N w) (n[_] : ForAllW n N)
      → ∣ transN n n[_] ∣ ≽ (⨆ ∣ n ∣ (∣_∣ ∘ n[_]))

-- Neighborhood generalisation of "Rm is transitive"
record Transitivity : Set where
  field
    transN     : (n : N w) → ForAllW n N → N w
    transN-sub : (n : N w) (n[_] : ForAllW n N)
      → ∣ transN n n[_] ∣ ⊆ ⨆ ∣ n ∣ (∣_∣ ∘ n[_])

  weakTransitivity : WeakTransitivity
  weakTransitivity = record
    { transN     = transN
    ; transN-ref = λ n n[_] {v} v∈J →
      let ((u , u∈n) , v∈n[u∈n]) = transN-sub n n[_] v∈J
       in v , ((u , u∈n) , v∈n[u∈n]) , ⊑-refl[ v ]
    }

record HyperTransitivity : Set where
  field
    transN       : (n : N w) → ForAllW n N → N w
    transN-equ : (n : N w) (n[_] : ForAllW n N)
      → ∣ transN n n[_] ∣ ≐ ⨆ ∣ n ∣ (∣_∣ ∘ n[_])

  transitivity : Transitivity
  transitivity = record
    { transN     = transN
    ; transN-sub = λ n n[_] → fst (transN-equ n n[_])
    }

-- all worlds have a neighborhood
record Seriality : Set where
  field
    -- the "unit" neighborhood
    unitN[_] : ∀ w → N w

-- all worlds have an empty neighborhood
record EmptySeriality : Set where
  field
    -- the "empty" neighborhood
    emptyN[_] : ∀ w → N w

    -- no world belongs to the empty neighborhood
    emptyN-sub : ∣ emptyN[ w ] ∣ ⊆ ∅

-- all neighborhoods are non-empty
record NonEmpty : Set where
  field
    N-prp : (n : N w) → ∃ λ v → v ∈ n

-- Weakly closed under intersection
record WeaklyClosedUnderInt : Set where
  field
    _⊗_   : N w → N w → N w
    ⊗-ref : (n1 n2 : N w) → ∣ n1 ∣ ≼ ∣ n1 ⊗ n2 ∣ × ∣ n1 ⊗ n2 ∣ ≽ ∣ n2 ∣

-- Closure under insersection
-- n1, n2 ∈ N w implies n1 ∩ n2 ∈ N w
record ClosedUnderInt : Set where
  field
    _⊗_   : N w → N w → N w
    ⊗-sub : (n1 n2 : N w) →  ∣ n1 ⊗ n2 ∣ ⊆ ∣ n1 ∣ ∩ ∣ n2 ∣

  weaklyClosedUnderInt : WeaklyClosedUnderInt
  weaklyClosedUnderInt = record
    { _⊗_   = _⊗_
    ; ⊗-ref = λ n1 n2 →
      (λ v∈n1⊗n2 → (-, (⊗-sub n1 n2 v∈n1⊗n2 .fst , ⊑-refl)))
      , λ v∈n1⊗n2 → (-, (⊗-sub n1 n2 v∈n1⊗n2 .snd , ⊑-refl))
    }

-- Closure under union
-- n1, n2 ∈ N w implies n1 ∪ n2 ∈ N w
record ClosedUnderUni : Set where
  field
    _⊕_   : N w → N w → N w
    ⊕-sub : (n1 n2 : N w) → ∣ n1 ⊕ n2 ∣ ⊆ ∣ n1 ∣ ∪ ∣ n2 ∣

record CoInclusion : Set where
  field
    N-ref : (n : N w) → ∣ n ∣ ⊆ (↓ w)

record WeakCoIdentity : Set where
  field
    N-prp : ∀ (n : N w) → ExistsW n (↓ w)

record CoIdentity : Set where
  field
    N-prp : ∀ (n : N w) → w ∈ n

  weakCoIdentity : WeakCoIdentity
  weakCoIdentity = record { N-prp = λ n → (-, N-prp n , ⊑-refl) }

record WeakDensity : Set where
  field
    -- the neighborhood family (ever neighborhood's members has a neighborhood)
    nFam     : ∀ (n : N w) → ForAllW n N
    nFam-ref : {n : N w} {v : W} (p : v ∈ n) → ∣ nFam n p ∣ ⊆ (↑ v)

record Density : Set where
  field
    nFam     : ∀ (n : N w) → ForAllW n N
    nFam-sub : {n : N w} {v : W} (p : v ∈ n) → ∣ nFam n p ∣ ⊆ ⟨ v ⟩

  weakDensity : WeakDensity
  weakDensity = record
    { nFam               = nFam
    ; nFam-ref = λ p x → ≡-subst (_ ⊑_) (nFam-sub p x) ⊑-refl
    }
