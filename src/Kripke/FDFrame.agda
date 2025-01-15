{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

-- Factorising Diamond Frame
module Kripke.FDFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) (_R_ : W → W → Set) where

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst) renaming (refl to ≡-refl)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import PUtil

_R-×_ : W → (W → Set) → Set
w R-× A = ∃ λ v → w R v × A v

witW : {w : W} {A : W → Set} → w R-× A → W
witW = fst

witR : {w : W} {A : W → Set} → (r : w R-× A) → w R (witW r)
witR r = r . snd .fst

-- 'E' for element
witE : {w : W} {A : W → Set} → (r : w R-× A) → A (witW r)
witE r = r . snd .snd

_D_ : W → W → Set
w D v = w R-× (v ⊆_)

wit⊆ : {w v : W} → (r : w D v) → v ⊆ (witW r)
wit⊆ = witE

-- Diamond Frame
record DFrame : Set where

  open IFrame IF public

  --
  -- Factorisation conditions
  --

  field
      factor : {w w' v : W} → w ⊆ w' → w R v → w' D v

  factorW : {w w' v : W} → (i : w ⊆ w') (r : w R v) → W       ; factorW w r = witW (factor w r)
  factorR : {w w' v : W} → (i : w ⊆ w') (r : w R v) → w' R _  ; factorR w r = witR (factor w r)
  factor⊆ : {w w' v : W} → (i : w ⊆ w') (r : w R v) → v ⊆ _   ; factor⊆ w r = wit⊆ (factor w r)

  R-to-D : {w v : W} → w R v → w D v
  R-to-D r = (-, r , ⊆-refl)

  _∙ᵢ_ : {w v v' : W} → w D v' → v ⊆ v' → w D v
  d ∙ᵢ i = witW d , witR d , ⊆-trans i (wit⊆ d)

  _ᵢ∙_ : {w w' v : W} → w ⊆ w' → w D v → w' D v
  i ᵢ∙ d = factor i (witR d) ∙ᵢ (wit⊆ d)

  field
    factor-pres-⊆-refl  : {w v : W}
      → (r : w R v) → factor ⊆-refl r ≡ R-to-D r
    factor-pres-⊆-trans : {w w' w'' v : W} → (i : w ⊆ w') (i' : w' ⊆ w'') (r : w R v)
      → factor (⊆-trans i i') r ≡ i' ᵢ∙ factor i r

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

  record PointedDFrame : Set where
    field
      R-point[_]   : (w : W) → w D w
      factor-pres-point : {w w' : W} (i : w ⊆ w') → i ᵢ∙ R-point[ w ] ≡ R-point[ w' ] ∙ᵢ i

    R-point : {w : W} → w D w ; R-point {w} = R-point[ w ]

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

  record InclusivePointedDFrame (IDF : InclusiveDFrame) (PDF : PointedDFrame) : Set where
    open InclusiveDFrame IDF
    open PointedDFrame PDF

    field
      R-to-⊆-pres-point : {w : W} → R-to-⊆ (witR R-point[ w ]) ≡ wit⊆ R-point[ w ]
