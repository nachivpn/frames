{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

-- Factorising Diamond Frame
module Kripke.FDFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) (_R_ : W → W → Set) where

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst) renaming (refl to ≡-refl)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import PUtil

-- Diamond Frame
record DFrame : Set where

  open IFrame IF public

  --
  -- Factorisation conditions
  --

  field
      factor : {w w' v : W} → w ⊆ w' → w R v → ∃ λ v' → w' R v' × v ⊆ v'

  factorW : {w w' v : W} → (i : w ⊆ w') (r : w R v) → W       ; factorW  w r = factor w r .fst
  factorR : {w w' v : W} → (i : w ⊆ w') (r : w R v) → w' R _  ; factorR  w r = factor w r .snd .fst
  factor⊆ : {w w' v : W} → (i : w ⊆ w') (r : w R v) → v ⊆ _   ; factor⊆ w r = factor w r .snd .snd

  field
    factor-pres-⊆-refl  : {w v : W}
      → (m : w R v) → factor ⊆-refl m ≡ (v , m , ⊆-refl)
    factor-pres-⊆-trans : {w w' w'' v : W} → (i : w ⊆ w') (i' : w' ⊆ w'') (m : w R v)
      → factor (⊆-trans i i') m ≡ (-, factorR i' (factorR i m) , ⊆-trans (factor⊆ i m) (factor⊆ i' (factorR i m)))

-- Definitions of diamond frames with additional properties
module Definitions (DF : DFrame) where

  open DFrame DF

  record InclusiveDFrame : Set where
    field
      R-to-⊆             : {w v : W} → w R v → w ⊆ v
      -- obs.: this condition says the factorisation square commutes under inclusion (R-to-⊆) 
      factor-pres-R-to-⊆ : {w w' v : W} → (i : w ⊆ w') (r : w R v) → ⊆-trans i (R-to-⊆ (factorR i r)) ≡ ⊆-trans (R-to-⊆ r) (factor⊆ i r)

  record ReflexiveDFrame : Set where
    field
      R-refl[_]          : (w : W) → w R w
      factor-pres-R-refl : {w w' : W} (i : w ⊆ w') → factor i R-refl[ w ] ≡ (w' , R-refl[ w' ] , i)

    R-refl : {w : W} → w R w ; R-refl = R-refl[ _ ]

  record TransitiveDFrame : Set where
    field
      R-trans             : {w w' w'' : W} → w R w' → w' R w'' → w R w''
      factor-pres-R-trans : {w w' u v : W} (i : w ⊆ w') (m : w R v) (m' : v R u)
        → factor i (R-trans m m') ≡ (-, R-trans (factorR i m) (factorR (factor⊆ i m) m') , factor⊆ (factor⊆ i m) m')
      R-trans-assoc : {v0 v1 v2 v3 : W} → (r : v0 R v1) (r' : v1 R v2) (r'' : v2 R v3) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r'')

  record SerialDFrame : Set where
    field
      R-serial[_]  : (w : W) → ∃ λ v → w R v

    R-serial : {w : W} → ∃ λ v → w R v ; R-serial {w} = R-serial[ w ]
    
    serialW  : (w : W) → W ; serialW w = R-serial[ w ] .fst
    serialR  : (w : W) → w R (serialW w) ; serialR w = R-serial[ w ] .snd

    field
      factor-pres-serial' : {w w' : W} (i : w ⊆ w') → (-, factorR i (serialR w)) ≡ R-serial[ w' ]

    serialW-pres-⊆ : {w w' : W} (i : w ⊆ w') → serialW w ⊆ serialW w'
    serialW-pres-⊆ {w} {w'} i = subst (_ ⊆_) (Σ-≡,≡←≡ (factor-pres-serial' i) .fst) (factor⊆ i (serialR w))

    opaque
      factor-pres-serial : {w w' : W} (i : w ⊆ w') → factor i (serialR w) ≡ (serialW w' , serialR w' , serialW-pres-⊆ i)
      factor-pres-serial i = let (p , q) = Σ-≡,≡←≡ (factor-pres-serial' i) in Σ×-≡,≡,≡→≡ (p , q , ≡-refl)

  record InclusiveReflexiveDFrame (IDF : InclusiveDFrame) (RDF : ReflexiveDFrame) : Set where
    open InclusiveDFrame IDF
    open ReflexiveDFrame RDF

    field
      R-to-⊆-pres-refl  : {w : W} → R-to-⊆ R-refl[ w ] ≡ ⊆-refl

  record InclusiveTransitiveDFrame (IDF : InclusiveDFrame) (TDF : TransitiveDFrame) : Set where
    open InclusiveDFrame IDF
    open TransitiveDFrame TDF

    field
      R-to-⊆-pres-trans : ∀ {w v u} → (r : w R v) →  (r' : v R u) → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r')

  record ReflexiveTransitiveDFrame (RDF : ReflexiveDFrame) (TDF : TransitiveDFrame) : Set where
    open ReflexiveDFrame RDF
    open TransitiveDFrame TDF

    field
      R-refl-unit-right : {w v : W} (r : w R v) → R-trans r R-refl ≡ r
      R-refl-unit-left  : {w v : W} (r : w R v) → R-trans R-refl r ≡ r
