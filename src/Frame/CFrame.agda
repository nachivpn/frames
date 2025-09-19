{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF

open import Data.Unit using (⊤)
open import Function using (const ; flip ; _∘_)

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
  (K   : W → Set)
  -- `v ∈ (k : K w)` means v is in the cover k
  (_∈_ : (v : W) {w : W} → K w → Set)
  -- wkK is functorial
  --(wkK : {w w' : W} → w ⊆ w' → K w → K w')
  --(wkK-pres-refl  : {w : W} (k : K w) → wkK ⊆-refl[ w ] k ≡ k)
  --(wkK-pres-trans : {w w' w'' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (k : K w) → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k))
  where

  -- a predicate is satisfied by all elements of a cover
  ForAllW : (k : K w) (P : W → Set) → Set
  ForAllW k P = ∀ {v} → v ∈ k → P v

  AllForW : (P : W → Set) (k : K w) → Set
  AllForW P k = ForAllW k P

  -- a predicate is satisfied by all proofs witnessing membership of a cover
  ForAll∈ : (k : K w) (P : ∀ {v} → v ∈ k → Set) → Set
  ForAll∈ k P = ∀ {v} → (p : v ∈ k) → P p

  -- a predicate is satisfied by all proofs witnessing membership of a cover
  Exists∈ : (k : K w) (P : ∀ {v} → v ∈ k → Set) → Set
  Exists∈ k P = ∃₂ λ v (p : v ∈ k) → P p

  -- inclusion of covers
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

  --
  ForAllW≋ : (k : K w) {P : W → Set} → (f : ForAllW k P) (g : ForAllW k P) →  Set
  ForAllW≋  {w} k f g = ForAll∈ k λ p → f p ≡ g p

  ForAllW≋' : {k k' : K w} {P : W → Set} → k ≡ k' → (f : ForAllW k P) (g : ForAllW k' P) →  Set
  ForAllW≋' {k = k} {k'} {P} k≡k' f g = ForAllW≋ k' (≡-subst (AllForW P) k≡k' f) g

  module _ {k : K w} {P : W → Set}  where

    ForAllW≋-refl : (f : ForAllW k P) → ForAllW≋ k f f
    ForAllW≋-refl f = λ _p → ≡-refl

    ForAllW≋-sym : {f f' : ForAllW k P} → ForAllW≋ k f f' → ForAllW≋ k f' f
    ForAllW≋-sym f≡f' = λ p → ≡-sym (f≡f' p)

    ForAllW≋-trans : {f f' f'' : ForAllW k P} → ForAllW≋ k f f' → ForAllW≋ k f' f'' → ForAllW≋ k f f''
    ForAllW≋-trans f≡f' f'≡f'' = λ p → ≡-trans (f≡f' p) (f'≡f'' p)

  module _ {k : K w} {k' : K w'} where

    -- equality on cover inclusion proofs
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

  -- read `k ＠ v` for `k : K w`
  -- as "factorisation of a cover k at world v"
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

  -- functions mapping a coverage k to a "larger" cover k'
  _⇒＠_ : W → W → Set
  w ⇒＠ v = (k : K w) → Σ (K v) λ k' → k ⊆k k'

  _$k_ : (w ⇒＠ w') → K w → K w'
  h $k k = h k .fst

  _$⊆_ : (h : w ⇒＠ w') → (k : K w) → k ⊆k (h $k k)
  h $⊆ k = h k .snd

  -- extensional equality for ⇒＠
  _≋[⇒＠]_ : w ⇒＠ w' → w ⇒＠ w' → Set
  h ≋[⇒＠] h' = (k : K _{-w-}) → h k ≋[＠] h' k

  ≋[⇒＠]-refl : (h : w ⇒＠ w') → h ≋[⇒＠] h
  ≋[⇒＠]-refl h = λ k → ≋[＠]-refl (h k)

  ≋[⇒＠]-sym : {h h' : w ⇒＠ w'} → h ≋[⇒＠] h' → h' ≋[⇒＠] h
  ≋[⇒＠]-sym p = λ k → ≋[＠]-sym (p k)

  ≋[⇒＠]-trans : {h h' h'' : w ⇒＠ w'} → h ≋[⇒＠] h' → h' ≋[⇒＠] h'' → h ≋[⇒＠] h''
  ≋[⇒＠]-trans p q = λ k → ≋[＠]-trans (p k) (q k)

  -- (W, ⇒＠) forms a category
  ⇒＠-refl[_] : ∀ w → w ⇒＠ w
  ⇒＠-refl[ w ] = λ k → k , ⊆k-refl[ k ]

  ⇒＠-trans : w ⇒＠ w' → w' ⇒＠ w'' → w ⇒＠ w''
  ⇒＠-trans h h' = λ k → (h' $k (h $k k)) , ⊆k-trans (h $⊆ k) (h' $⊆ (h $k k))

  ⇒＠-trans-unit-left : (h : w ⇒＠ w') → ⇒＠-trans ⇒＠-refl[ w ] h ≋[⇒＠] h
  ⇒＠-trans-unit-left h = λ k → ≡-refl , ⊆k-trans-unit-left (h $⊆ k)

  ⇒＠-trans-unit-right : (h : w ⇒＠ w') → ⇒＠-trans h ⇒＠-refl[ w' ] ≋[⇒＠] h
  ⇒＠-trans-unit-right h = λ k → ≡-refl , ⊆k-trans-unit-right (h $⊆ k)

  ⇒＠-trans-assoc : (h : u ⇒＠ v) (h' : v ⇒＠ w) (h'' : w ⇒＠ w')
    → ⇒＠-trans (⇒＠-trans h h') h'' ≋[⇒＠] ⇒＠-trans h (⇒＠-trans h' h'')
  ⇒＠-trans-assoc h h' h'' = λ k
    → ≡-refl , ⊆k-trans-assoc (h $⊆ k) (h' $⊆ (h $k k)) (h'' $⊆ (h' $k (h $k k) ))

  module _ (Pi : W → W → Set) (strPi : {w v v' : W} → v ⊆ v' → Pi v' w → Pi v w) where

    strForAllW : {k : K w} (i : v ⊆ v') → ForAllW k (Pi v') → ForAllW k (Pi v)
    strForAllW i fam x = strPi i (fam x)

  module _ (P : W → Set) (wkP : {w w' : W} → w ⊆ w' → P w → P w') where

    wkForAllW : {k : K w} {k' : K w'} → k ⊆k k' → ForAllW k P → ForAllW k' P
    wkForAllW is fam x = let (_ , x' , i) = is x in wkP i (fam x')

  strForAllW⊆ : {k : K w} (i : v ⊆ v') → ForAllW k (v' ⊆_) → ForAllW k (v ⊆_)
  strForAllW⊆ i fam x = strForAllW _⊆_ ⊆-trans i fam x

  wkForAllW⊆ : {k : K w} {k' : K w'} → k ⊆k k' → ForAllW k (w ⊆_) → ForAllW k' (w ⊆_)
  wkForAllW⊆ is fam x = wkForAllW (_ ⊆_) (flip ⊆-trans) is fam x

  record CFrame : Set₁ where

    field

      factor : w ⊆ w' → w ⇒＠ w'

      factor-pres-refl :
          factor ⊆-refl ≋[⇒＠] ⇒＠-refl[ w ]

      factor-pres-trans : {w w' : W} (i : w ⊆ w') (i' : w' ⊆ w'')
        → factor (⊆-trans i i') ≋[⇒＠] ⇒＠-trans (factor i) (factor i')

    factorForAllK : {k : K w} {k' : K w'} → k ⊆k k' → ForAllW k K → ForAllW k' K
    factorForAllK is fam x = wkForAllW K (_$k_ ∘ factor) is fam x

  module _ (CF : CFrame) where

    open CFrame CF

    record Coverage : Set₁ where

      field

        -- a cover of w is a family of (w ⊆_) proofs
        family        : (k : K w) → ForAllW k (w ⊆_)

      field
        -- factorisation square commutes
        family-stable : (i : w ⊆ w') (k : K w)
          → ForAllW≋ _ (wkForAllW⊆ (factor i $⊆ k) (family k)) (strForAllW⊆ i (family (factor i $k k)))

    -- Identity condition
    record Pointed : Set where

      field

        -- a pointed cover
        pointK[_]     : ∀ w → K w

        -- only w can be covered by pointK[ w ]
        pointK-nec : ForAllW (pointK[ w ]) (w ≡_)

        -- w is covered by pointK[ w ]
        point∈-suf[_] : ∀ w → w ∈ pointK[ w ]

        -- uniqueness of identity proofs for pointK-single (retains --without-K, but is it worth it?)
        pointK-uip[_] : ∀ w → pointK-nec point∈-suf[ w ] ≡ ≡-refl

      --
      pointK-fam : {P : W → Set} → P w → ForAllW (pointK[ w ]) P
      pointK-fam p x = ≡-subst _ (pointK-nec x) p

      pointK-pres-⊆ : w ⊆ w' → pointK[ w ] ⊆k pointK[ w' ]
      pointK-pres-⊆ {w} {w'} i = λ x → w , point∈-suf[ w ] , ≡-subst (w ⊆_) (pointK-nec x) i

      -- canonical factorisation of pointK
      point＠[_] : w ⊆ w' → pointK[ w ] ＠ w'
      point＠[ i ] = pointK[ _ ] , pointK-pres-⊆ i

      field
        factor-pres-point : (i : w ⊆ w') → factor i pointK[ w ] ≋[＠] point＠[ i ]

    -- Transitivity condition
    record Joinable : Set₁ where

      field

        --
        joinK : (k : K w) → ForAllW k K → K w

        --
        join∈-nec : (k : K w) (h : ForAllW k K) → ForAllW (joinK k h) λ v' → Exists∈ k (v' ∈_ ∘ h)

        --
        join∈-suf : (k : K w) (h : ForAllW k K) → ForAll∈ k λ p → ForAllW (h p) (_∈ joinK k h)

        --
        joinK-pres-≋ : (k : K w) → {h h' : ForAllW k K} → ForAllW≋ k h h' → joinK k h ≡ joinK k h'

      -- type-casted join∈-nec
      join∈-nec' : (k : K w) (h : ForAllW k K)
        → {h' : ForAllW k K} (h≋h' : ForAllW≋ k h h')
        → ForAllW (joinK k h') (λ v → Exists∈ k (v ∈_ ∘ h'))
      join∈-nec' k h h≋h' {v} v∈joinh' = let
        v∈joinh = ≡-subst (v ∈_) (≡-sym (joinK-pres-≋ _ h≋h')) v∈joinh'
        (u , p∶u∈k , v∈h⟨p∶u∈k⟩) = join∈-nec k h v∈joinh
        in u , p∶u∈k ,  ≡-subst (v ∈_) (h≋h' p∶u∈k) v∈h⟨p∶u∈k⟩

      field
        --
        join∈-pres-≋ : {k : K w}  {h h' : ForAllW k K}
          → (h≋h' : ForAllW≋ k h h')
          → ForAllW≋ (joinK k h') (join∈-nec' k h h≋h') (join∈-nec k h')

      joinK-pres-⊆ : {k : K w} {k' : K w'} (h : ForAllW k K)
        → (is : k ⊆k k')
        → joinK k h ⊆k joinK k' (factorForAllK is h)
      joinK-pres-⊆ h is {v⋆ } p' =
        let (u , u∈k' , v⋆∈h') = join∈-nec _ (factorForAllK is h) p'
            (v , v∈k , v⊆u) = is u∈k'
            (x , y) = factor v⊆u (h v∈k)
            (a , b , c) = y v⋆∈h'
        in a , join∈-suf _ h v∈k b , c

      -- canonical factorisation of joinK
      join＠ : w ⊆ w' → (k : K w) → (h : ForAllW k K) → joinK k h ＠ w'
      join＠ i k h = let (k' , is) = factor i k ; h' = factorForAllK is h
        in joinK k' h' , joinK-pres-⊆ h is

      field
         factor-pres-join : (i : w ⊆ w') (k : K w) (h : ForAllW k K)
           → factor i (joinK k h) ≋[＠] join＠ i k h
