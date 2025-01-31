{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

-- Factorising Diamond Frame
module Kripke.FDFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) (_R_ : W → W → Set) where

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst) renaming (refl to ≡-refl)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import PUtil

-- for a given world `w : W` and a family of sets `A : W → Set`
-- `w R-× A` is a triple (v : W , r : w R v , x : A v)
_R-×_ : W → (W → Set) → Set
w R-× A = ∃ λ v → w R v × A v

-- projections of R-×
witW : {w : W} {A : W → Set} → w R-× A → W ; witW = fst
witR : {w : W} {A : W → Set} (r : w R-× A) → w R (witW r) ; witR r = r . snd .fst
witE : {w : W} {A : W → Set} (r : w R-× A) → A (witW r) ; witE r = r . snd .snd
-- 'E' in `witE` stands for "element"

-- composite relation R;⊇
_D_ : W → W → Set
w D v = w R-× (v ⊆_)

-- projection alias
wit⊆ : {w v : W} (r : w D v) → v ⊆ (witW r)
wit⊆ = witE

-- Diamond Frame
record DFrame : Set where

  open IFrame IF public

  --
  -- Factorisation conditions
  --

  field
    -- "(◇) functor action"
    factor : {w w' v : W} → w ⊆ w' → w R v → w' D v

  -- projections of the result of factorisation
  factorW : {w w' v : W} (i : w ⊆ w') (r : w R v) → W       ; factorW w r = witW (factor w r)
  factorR : {w w' v : W} (i : w ⊆ w') (r : w R v) → w' R _  ; factorR w r = witR (factor w r)
  factor⊆ : {w w' v : W} (i : w ⊆ w') (r : w R v) → v ⊆ _   ; factor⊆ w r = wit⊆ (factor w r)

  -- R ⊑ D
  R-to-D : {w v : W} → w R v → w D v
  R-to-D r = (-, r , ⊆-refl)

  -- D absorbs ⊇ on the right ("module condition")
  _∙ᵢ_ : {w v v' : W} → w D v' → v ⊆ v' → w D v
  d ∙ᵢ i = witW d , witR d , ⊆-trans i (wit⊆ d)

  -- D absorbs ⊇ on the left ("module condition")
  _ᵢ∙_ : {w w' v : W} → w ⊆ w' → w D v → w' D v
  i ᵢ∙ d = factor i (witR d) ∙ᵢ (wit⊆ d)

  -- "functor laws"
  field
    factor-pres-⊆-refl  : {w v : W}
      → (r : w R v) → factor ⊆-refl r ≡ R-to-D r
    factor-pres-⊆-trans : {w w' w'' v : W} (i : w ⊆ w') (i' : w' ⊆ w'') (r : w R v)
      → factor (⊆-trans i i') r ≡ i' ᵢ∙ factor i r

-- Definitions of diamond frames with additional properties
module Definitions (DF : DFrame) where

  open DFrame DF

  record InclusiveDFrame : Set where
    field
      -- R ⊑ ⊆, induces "strength on ◇"
      R-to-⊆             : {w v : W} → w R v → w ⊆ v

      -- factorisation square commutes under inclusion (R-to-⊆)
      factor-pres-R-to-⊆ : {w w' v : W} (i : w ⊆ w') (r : w R v)
        → ⊆-trans i (R-to-⊆ (factorR i r)) ≡ ⊆-trans (R-to-⊆ r) (factor⊆ i r)

  record ReflexiveDFrame : Set where
    field
      -- Id ⊑ R, induces "point on ◇"
      R-refl[_]          : (w : W) → w R w

      -- coherence between factorisability and reflexivity ("naturality of point")
      factor-pres-R-refl : {w w' : W} (i : w ⊆ w')
        → factor i R-refl[ w ] ≡ (w' , R-refl[ w' ] , i)

    R-refl : {w : W} → w R w ; R-refl = R-refl[ _ ]

  record TransitiveDFrame : Set where
    field
      -- R² ⊑ R, induces "join on ◇"
      R-trans             : {w w' w'' : W} → w R w' → w' R w'' → w R w''

      -- coherence between factorisability and transitivity ("naturality of join")
      factor-pres-R-trans : {w w' u v : W} (i : w ⊆ w') (m : w R v) (m' : v R u)
        → factor i (R-trans m m') ≡ (-, R-trans (factorR i m) (factorR (factor⊆ i m) m') , factor⊆ (factor⊆ i m) m')

      -- "associativity of join"
      R-trans-assoc : {v0 v1 v2 v3 : W} (r : v0 R v1) (r' : v1 R v2) (r'' : v2 R v3)
        → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r'')

  record PointedDFrame : Set where
    field
      -- Id ⊑ D, induces "point on ◇"
      R-point[_]   : (w : W) → w D w

      -- coherence between factorisability and pointedness ("naturality of point")
      factor-pres-R-point : {w w' : W} (i : w ⊆ w')
        → i ᵢ∙ R-point[ w ] ≡ R-point[ w' ] ∙ᵢ i

    R-point : {w : W} → w D w ; R-point {w} = R-point[ w ]

  record JoinableDFrame : Set where
    field
      -- R² ⊑ D, induces "join on ◇"
      R-join : {w u v : W} → w R u → u R v → w D v

    _ᵣ∙_ : {w u v : W} → w R u → u D v → w D v
    r ᵣ∙ d = R-join r (witR d) ∙ᵢ wit⊆ d

    _∙ᵣ_ : {w u v : W} → w D u → u R v → w D v
    d ∙ᵣ r = witR d ᵣ∙ factor (wit⊆ d) r

    field
      -- coherence between factorisability and joinability ("naturality of join")
      factor-pres-R-join : {w w' u v : W} (i : w ⊆ w') (r : w R v) (r' : v R u)
        → i ᵢ∙ R-join r r' ≡ factor i r ∙ᵣ r'
      -- ("associativity of join")
      R-join-assoc       : {w u v x : W} (r : w R u) (r' : u R v) (r'' : v R x)
        → r ᵣ∙ (R-join r' r'') ≡ (R-join r r') ∙ᵣ r''

  -- Coherence between inclusion and reflexivity
  record InclusiveReflexiveDFrame (IDF : InclusiveDFrame) (RDF : ReflexiveDFrame) : Set where
    open InclusiveDFrame IDF
    open ReflexiveDFrame RDF

    field
      R-to-⊆-pres-refl  : {w : W} → R-to-⊆ R-refl[ w ] ≡ ⊆-refl

  -- Coherence between inclusion and transitivity
  record InclusiveTransitiveDFrame (IDF : InclusiveDFrame) (TDF : TransitiveDFrame) : Set where
    open InclusiveDFrame IDF
    open TransitiveDFrame TDF

    field
      R-to-⊆-pres-trans : {w v u : W} (r : w R v) (r' : v R u)
        → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r')

  -- Coherence between reflexivity and transitivity
  record ReflexiveTransitiveDFrame (RDF : ReflexiveDFrame) (TDF : TransitiveDFrame) : Set where
    open ReflexiveDFrame RDF
    open TransitiveDFrame TDF

    field
      R-trans-unit-right : {w v : W} (r : w R v) → R-trans r R-refl ≡ r
      R-trans-unit-left  : {w v : W} (r : w R v) → R-trans R-refl r ≡ r

  -- Coherence between inclusion and pointedness
  record InclusivePointedDFrame (IDF : InclusiveDFrame) (PDF : PointedDFrame) : Set where
    open InclusiveDFrame IDF
    open PointedDFrame PDF

    field
      R-to-⊆-pres-R-point : {w : W} → R-to-⊆ (witR R-point[ w ]) ≡ wit⊆ R-point[ w ]

  -- Coherence between inclusion and joinability
  record InclusiveJoinableDFrame (IDF : InclusiveDFrame) (JDF : JoinableDFrame) : Set where
    open InclusiveDFrame IDF
    open JoinableDFrame JDF

    field
      R-to-⊆-pres-join : {w u v : W} (r : w R u) (r' : u R v)
        → R-to-⊆ (witR (R-join r r')) ≡ ⊆-trans (⊆-trans (R-to-⊆ r) (R-to-⊆ r')) (wit⊆ (R-join r r'))

  -- Coherence between pointedness and joinability
  record MonadicDFrame (PDF : PointedDFrame) (JDF : JoinableDFrame) : Set where
    open PointedDFrame PDF
    open JoinableDFrame JDF

    field
      R-join-unit-left  : {w v : W} (r : w R v) → R-point[ w ] ∙ᵣ r ≡ R-to-D r
      R-join-unit-right : {w v : W} (r : w R v) → r ᵣ∙ R-point[ v ] ≡ R-to-D r
