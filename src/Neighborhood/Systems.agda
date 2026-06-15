{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Lib as Lib

-- Definitions of various neighborhood "systems"
module Neighborhood.Systems {W : Set} {_⊆_ : W → W → Set} (𝕎 : Preorder W _⊆_) where

record NeighborhoodSystem : Set₁ where
  field

    -- neighborhoods
    N   : W → Set
    _∈_ : (v : W) {w : W} → N w → Set

  open Lib 𝕎 N _∈_ public

  field
    refinement  : Refinement

  open Refinement refinement public

module _ (NS : NeighborhoodSystem) where

  open NeighborhoodSystem NS

  record WeakCoverSystem : Set where

    field
      inclusion    : Inclusion
      identity     : WeakIdentity
      transitivity : WeakTransitivity
                   
    open Inclusion inclusion public
    open WeakIdentity identity public
    open WeakTransitivity transitivity public

  record CoverSystem : Set where

    field
      inclusion    : Inclusion
      identity     : Identity
      transitivity : Transitivity

    weakCoverSystem : WeakCoverSystem
    weakCoverSystem = record
      { inclusion    = inclusion
      ; identity     = Identity.weakIdentity identity
      ; transitivity = Transitivity.weakTransitivity transitivity
      }
      
    open Inclusion inclusion public
    open Identity identity public
    open Transitivity transitivity public
    
  record SLModalSystem : Set where
    field
      inclusion  : Inclusion
      
  record CKBoxModalSystem : Set where
    field
      intclosed : WeaklyClosedUnderInt
      seriality  : Seriality

    open Seriality seriality public
    open WeaklyClosedUnderInt intclosed  public

  record MaybeModalSystem : Set where
    field
      coverSystem : CoverSystem
      nothingness : EmptySeriality

    open CoverSystem coverSystem public
    
PLLModalSystem = WeakCoverSystem
module PLLModalSystem = WeakCoverSystem
