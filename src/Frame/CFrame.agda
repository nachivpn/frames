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

open import Function using (id ; _∘_)

open import PUtil using (Σ×-≡,≡,≡→≡)

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

  -- extensional equality of ForAllW proofs
  ForAllW≋ : (k : K w) {P : W → Set} → (f : ForAllW k P) (g : ForAllW k P) →  Set
  ForAllW≋  {w} k f g = ForAll∈ k λ p → f p ≡ g p

  -- ForAllW≋ is an equivalence
  module _ {k : K w} {P : W → Set}  where

    ForAllW≋-refl : (f : ForAllW k P) → ForAllW≋ k f f
    ForAllW≋-refl f = λ _p → ≡-refl

    ForAllW≋-sym : {f f' : ForAllW k P} → ForAllW≋ k f f' → ForAllW≋ k f' f
    ForAllW≋-sym f≡f' = λ p → ≡-sym (f≡f' p)

    ForAllW≋-trans : {f f' f'' : ForAllW k P} → ForAllW≋ k f f' → ForAllW≋ k f' f'' → ForAllW≋ k f f''
    ForAllW≋-trans f≡f' f'≡f'' = λ p → ≡-trans (f≡f' p) (f'≡f'' p)

  -- extensional equality of neighborhood ordering
  module _ {k : K w} {k' : K w'} where

    _≋[⊆k]_ : k ⊆k k' → k ⊆k k' → Set
    _≋[⊆k]_ = ForAllW≋ k'

    ≋[⊆k]-refl : (is : k ⊆k k') → is ≋[⊆k] is
    ≋[⊆k]-refl = ForAllW≋-refl

    ≋[⊆k]-sym : {is is' : k ⊆k k'} → is ≋[⊆k] is' → is' ≋[⊆k] is
    ≋[⊆k]-sym = ForAllW≋-sym

    ≋[⊆k]-trans : {is is' is'' : k ⊆k k'} → is ≋[⊆k] is' → is' ≋[⊆k] is'' → is ≋[⊆k] is''
    ≋[⊆k]-trans = ForAllW≋-trans

  ⊆k-trans-unit-left : {k : K w} {k' : K w'} (is : k ⊆k k')
    → ⊆k-trans ⊆k-refl[ k ] is ≋[⊆k] is
  ⊆k-trans-unit-left is p = let (_ , _ , i) = is p
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-unit-left i)

  ⊆k-trans-unit-right : {k : K w} {k' : K w'} (is : k ⊆k k')
    → ⊆k-trans is ⊆k-refl[ k' ] ≋[⊆k] is
  ⊆k-trans-unit-right is p = let (_ , _ , i) = is p
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-unit-right i)

  ⊆k-trans-assoc : {k : K u} {k' : K v} {k'' : K w} {k''' : K w'}
    → (is : k ⊆k k') (is' : k' ⊆k k'') (is'' : k'' ⊆k k''')
    → ⊆k-trans (⊆k-trans is is') is'' ≋[⊆k] ⊆k-trans is (⊆k-trans is' is'')
  ⊆k-trans-assoc is is' is'' p''' = let
    (_ , p'' , i'') = is'' p'''
    (_ , p' , i')   = is' p''
    (_ , _ , i)     = is p'
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-assoc i i' i'')

  -- "factorisation of k @ v"
  _＠_ : K w → W → Set
  k ＠ v = Σ (K v) λ k' → k ⊆k k'

  module _ {k : K w} {w' : W} where

    _≋[＠]_ : k ＠ w' → k ＠ w' → Set
    (k1' , is1) ≋[＠] (k2' , is2) = Σ (k1' ≡ k2') λ k1≡k2 → ≡-subst (_{-k-} ⊆k_) k1≡k2 is1 ≋[⊆k] is2

    ≋[＠]-refl : (x : k ＠ w') → x ≋[＠] x
    ≋[＠]-refl (k , is) = ≡-refl {x = k} , ≋[⊆k]-refl is

    ≋[＠]-sym : {x y : k ＠ w'} → x ≋[＠] y → y ≋[＠] x
    ≋[＠]-sym (≡-refl , is≋is') = ≡-refl , ≋[⊆k]-sym is≋is'

    ≋[＠]-trans : {x y z : k ＠ w'} → x ≋[＠] y → y ≋[＠] z → x ≋[＠] z
    ≋[＠]-trans (≡-refl , is≋is') (≡-refl , is'≋is'') = ≡-refl , ≋[⊆k]-trans is≋is' is'≋is''

  -- factorising function
  _⇒k_ : W → W → Set
  w ⇒k v = (k : K w) → k ＠ v

  -- restriction of a factorisation function
  -- to the first component of its result
  _$k_ : (w ⇒k w') → K w → K w'
  h $k k = h k .fst

  -- restriction of a factorisation function
  -- to the second component of its result
  _$⊆_ : (h : w ⇒k w') → (k : K w) → k ⊆k (h $k k)
  h $⊆ k = h k .snd

  -- extensional equality for factorising functions
  _≋[⇒k]_ : w ⇒k w' → w ⇒k w' → Set
  h ≋[⇒k] h' = (k : K _{-w-}) → h k ≋[＠] h' k

  ≋[⇒k]-refl : (h : w ⇒k w') → h ≋[⇒k] h
  ≋[⇒k]-refl h = λ k → ≋[＠]-refl (h k)

  ≋[⇒k]-sym : {h h' : w ⇒k w'} → h ≋[⇒k] h' → h' ≋[⇒k] h
  ≋[⇒k]-sym p = λ k → ≋[＠]-sym (p k)

  ≋[⇒k]-trans : {h h' h'' : w ⇒k w'} → h ≋[⇒k] h' → h' ≋[⇒k] h'' → h ≋[⇒k] h''
  ≋[⇒k]-trans p q = λ k → ≋[＠]-trans (p k) (q k)

  -- (W, ⇒k) forms a category
  ⇒k-refl[_] : ∀ w → w ⇒k w
  ⇒k-refl[ w ] = λ k → k , ⊆k-refl[ k ]

  ⇒k-trans : w ⇒k w' → w' ⇒k w'' → w ⇒k w''
  ⇒k-trans h h' = λ k → (h' $k (h $k k)) , ⊆k-trans (h $⊆ k) (h' $⊆ (h $k k))

  ⇒k-trans-unit-left : (h : w ⇒k w') → ⇒k-trans ⇒k-refl[ w ] h ≋[⇒k] h
  ⇒k-trans-unit-left h = λ k → ≡-refl , ⊆k-trans-unit-left (h $⊆ k)

  ⇒k-trans-unit-right : (h : w ⇒k w') → ⇒k-trans h ⇒k-refl[ w' ] ≋[⇒k] h
  ⇒k-trans-unit-right h = λ k → ≡-refl , ⊆k-trans-unit-right (h $⊆ k)

  ⇒k-trans-assoc : (h : u ⇒k v) (h' : v ⇒k w) (h'' : w ⇒k w')
    → ⇒k-trans (⇒k-trans h h') h'' ≋[⇒k] ⇒k-trans h (⇒k-trans h' h'')
  ⇒k-trans-assoc h h' h'' = λ k
    → ≡-refl , ⊆k-trans-assoc (h $⊆ k) (h' $⊆ (h $k k)) (h'' $⊆ (h' $k (h $k k) ))

  record CFrame : Set₁ where

    field

      -- i.e. factor : w ⊆ w' → (k : K w) → Σ (K w') λ k' → k ⊆k k'
      factor : w ⊆ w' → w ⇒k w'

      --
      -- factor is functorial in its first argument
      --
      factor-pres-refl :
          factor ⊆-refl ≋[⇒k] ⇒k-refl[ w ]
      factor-pres-trans : {w w' : W} (i : w ⊆ w') (i' : w' ⊆ w'')
        → factor (⊆-trans i i') ≋[⇒k] ⇒k-trans (factor i) (factor i')

  module _ (CF : CFrame) where

    open CFrame CF

    record Coverage : Set₁ where

      field

        -- "Covering family"
        -- Every neighbor in a neighborhood is reachable via ⊆
        cfamily        : (k : K w) → ForAllW k (w ⊆_)

      strFam : {k : K w} (i : v ⊆ v') → ForAllW k (v' ⊆_) → ForAllW k (v ⊆_)
      strFam i fam x = ⊆-trans i (fam x)

      wkFam : {k : K w} {k' : K w'} → k ⊆k k' → ForAllW k (w ⊆_) → ForAllW k' (w ⊆_)
      wkFam is fam x = let (_ , x' , i) = is x in ⊆-trans (fam x') i

      field
        -- factorisation square commutes
        family-stable : (i : w ⊆ w') (k : K w)
          → ForAllW≋ _ (wkFam (factor i $⊆ k) (cfamily k)) (strFam i (cfamily (factor i $k k)))

    record Pointed : Set where

      field

        -- a "pointed" neighborhood
        pointK[_]     : ∀ w → K w

        -- w is a member of pointK[ w ]
        point∈[_]     : ∀ w → w ∈ pointK[ w ]

        -- every neighbor in pointK is an intuitionistic future of w reachable through ⊆
        pointK-family : ForAllW (pointK[ w ]) (w ⊆_ )

        -- coherence condition on pointed neighborhoods
        -- i.e. reaching w (as its own neighbor) via pointK-family must be through ⊆-refl
        pointK-coh[_] : ∀ w → pointK-family point∈[ w ] ≡ ⊆-refl[ w ]

      pointK-pres-⊆ : w ⊆ w' → pointK[ w ] ⊆k pointK[ w' ]
      pointK-pres-⊆ {w} {w'} i = λ x → w , point∈[ w ] , ⊆-trans i (pointK-family x)

      -- canonical factorisation of pointK[ w ] at w'
      point＠[_] : w ⊆ w' → pointK[ w ] ＠ w'
      point＠[ i ] = pointK[ _ ] , pointK-pres-⊆ i

      field
        -- factor preserves "identity" in its second argument
        factor-pres-point : (i : w ⊆ w') → factor i pointK[ w ] ≋[＠] point＠[ i ]
