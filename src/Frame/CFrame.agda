{-# OPTIONS --safe #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF

open import Data.Unit using (⊤)
open import Function using (flip ; _∘_)

open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Unary using () renaming (Pred to Predℓ ; _⊆_ to _⊑_)
open import Level using (0ℓ)

open import PUtil using (Σ×-≡,≡,≡→≡)
open import HEUtil

private
  variable
    w w' w'' u u' v v' : W

Pred : Set → Set₁
Pred A = Predℓ A 0ℓ

module Core
  -- Neighborhood "directory"
  (N   : W → Set)
  -- Membership relation
  -- v ∈ α means v is in the neighborhood α (of w)
  (_∈_ : (v : W) {w : W} → N w → Set)
  where

  _∋_ : {w : W} → N w → Pred W
  α ∋ v = v ∈ α

  -- a predicate satisfied by all elements of a neighborhood
  ForAllW : (α : N w) (P : Pred W) → Set
  ForAllW α P = (α ∋_) ⊑ P

  -- ForAllW flipped
  AllForW : (P : Pred W) (α : N w) → Set
  AllForW P α = ForAllW α P

  -- a predicate satisfied by all proofs witnessing membership
  ForAll∈ : (α : N w) (P : ∀ {v} → v ∈ α → Set) → Set
  ForAll∈ α P = ∀ {v} → (p : v ∈ α) → P p

  -- a predicate is satisfied by all proofs witnessing membership of a cover
  ExistsW : (α : N w) (P : Pred W) → Set
  ExistsW α P = ∃ λ v → v ∈ α × P v

  -- a predicate is satisfied by all proofs witnessing membership of a cover
  Exists∈ : (α : N w) (P : ∀ {v} → v ∈ α → Set) → Set
  Exists∈ α P = ∃₂ λ v (p : v ∈ α) → P p

  -- refinement relation for neighborhoods
  _≼_ : N w → N w' → Set
  α ≼ α' = ForAllW α' (λ v' → ∃ λ v → v ∈ α × (v ⊆ v'))

  ≼-refl[_] : (α : N w) → α ≼ α
  ≼-refl[ α ] {v} p = v , p , ⊆-refl[ v ]

  ≼-trans : {α : N w} {α' : N w'} {α'' : N w''}
    → α ≼ α' → α' ≼ α'' → α ≼ α''
  ≼-trans is is' {v''} p'' = let
    (v' , p' , i') = is' p''
    (v , p , i)    = is p'
    in (v , p , ⊆-trans i i')

  -- extensional equality of ForAllW proofs
  ForAllW≡ : (α : N w) {P : Pred W} → (f : ForAllW α P) (g : ForAllW α P) → Set
  ForAllW≡  {w} α f g = ForAll∈ α λ p → f p ≡ g p

  -- ForAllW≡ is an equivalence
  module _ {α : N w} {P : Pred W}  where

    ForAllW≡-refl : (f : ForAllW α P) → ForAllW≡ α f f
    ForAllW≡-refl f = λ _p → ≡-refl

    ForAllW≡-sym : {f f' : ForAllW α P} → ForAllW≡ α f f' → ForAllW≡ α f' f
    ForAllW≡-sym f≡f' = λ p → ≡-sym (f≡f' p)

    ForAllW≡-trans : {f f' f'' : ForAllW α P} → ForAllW≡ α f f' → ForAllW≡ α f' f'' → ForAllW≡ α f f''
    ForAllW≡-trans f≡f' f'≡f'' = λ p → ≡-trans (f≡f' p) (f'≡f'' p)

  ForAllW≅ : {α α' : N w} {P : Pred W} → (f : ForAllW α P) (f' : ForAllW α' P) →  Set
  ForAllW≅ {w} {α} {α'} f f' = α ≡ α' × ∀ {v} {p : v ∈ α} {p' : v ∈ α'} → p ≅ p' → f p ≡ f' p'

  -- ForAllW≡ is an equivalence
  module _ {P : Pred W}  where

    ForAllW≅-refl : {α : N w} (f : ForAllW α P) → ForAllW≅ f f
    ForAllW≅-refl f = ≡-refl , λ p → ≡-cong f (≅-to-≡ p)

    ForAllW≅-sym : {α α' : N w} {f : ForAllW α P} {f' : ForAllW α' P} → ForAllW≅ f f' → ForAllW≅ f' f
    ForAllW≅-sym (α≡α' , f≅f') = ≡-sym α≡α' , λ x → ≡-sym (f≅f' (≅-sym x))

    ForAllW≅-trans : {α α' α'' : N w} {f : ForAllW α P} {f' : ForAllW α' P} {f'' : ForAllW α'' P}
      → ForAllW≅ f f' → ForAllW≅ f' f'' → ForAllW≅ f f''
    ForAllW≅-trans (≡-refl , f≅f') (α'≡α'' , f'≅f'') =  α'≡α''
      , λ x → ≡-trans (f≅f' ≅-refl) (f'≅f'' x)

  Exists∈≅ : {α α' : N w} {P : ∀ {v} → v ∈ α → Set} {P' : ∀ {v} → v ∈ α' → Set}
    → (x : Exists∈ α P) (y : Exists∈ α' P') → Set
  Exists∈≅ {w} {α} {α'} (v , p , q) (v' , p' , q') = v ≡ v' × p ≅ p' × q ≅ q'

  Exists∈≅-refl : {α : N w} {P : ∀ {v} → v ∈ α → Set} (x : Exists∈ α P)
    → Exists∈≅ x x
  Exists∈≅-refl x = ≡-refl , ≅-refl , ≅-refl

  Exists∈≅-sym : {α α' : N w} {P : ∀ {v} → v ∈ α → Set} {P' : ∀ {v} → v ∈ α' → Set}
    → {x : Exists∈ α P} {y : Exists∈ α' P'}
    → Exists∈≅ x y → Exists∈≅ y x
  Exists∈≅-sym (q , r , s) = ≡-sym q , ≅-sym r , ≅-sym s

  Exists∈≅-trans : {α α' α'' : N w}
    → {P : ∀ {v} → v ∈ α → Set} {P' : ∀ {v} → v ∈ α' → Set} {P'' : ∀ {v} → v ∈ α'' → Set}
    → {x : Exists∈ α P} {y : Exists∈ α' P'} {z : Exists∈ α'' P''}
    → Exists∈≅ x y → Exists∈≅ y z → Exists∈≅ x z
  Exists∈≅-trans (q₁ , r₁ , s₁) (q₂ , r₂ , s₂)
    = ≡-trans q₁ q₂ , ≅-trans r₁ r₂ , ≅-trans s₁ s₂

  -- extensional equality of refinement proofs
  module _ {α : N w} where

    _≋[≼]_ : {α' α'' : N w'} → α ≼ α' → α ≼ α'' → Set
    _≋[≼]_ = ForAllW≅

    ≋[≼]-refl : {α' : N w'} → (is : α ≼ α') → is ≋[≼] is
    ≋[≼]-refl = ForAllW≅-refl

    ≋[≼]-sym : {α' α'' : N w'} → {is : α ≼ α'} {is' : α ≼ α''} → is ≋[≼] is' → is' ≋[≼] is
    ≋[≼]-sym = ForAllW≅-sym

    ≋[≼]-trans : {α' α'' α''' : N w'} → {is : α ≼ α'} {is' : α ≼ α''} {is'' : α ≼ α'''}
      → is ≋[≼] is' → is' ≋[≼] is'' → is ≋[≼] is''
    ≋[≼]-trans = ForAllW≅-trans

  ≼-trans-unit-left : {α : N w} {α' : N w'} (is : α ≼ α')
    → ≼-trans ≼-refl[ α ] is ≋[≼] is
  ≼-trans-unit-left is = ≡-refl , λ { {v} {p} {.p} ≅-refl → let (_ , _ , i) = is p
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-unit-left i) }

  ≼-trans-unit-right : {α : N w} {α' : N w'} (is : α ≼ α')
    → ≼-trans is ≼-refl[ α' ] ≋[≼] is
  ≼-trans-unit-right is = ≡-refl , λ { {v} {p} {.p} ≅-refl → let (_ , _ , i) = is p
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-unit-right i) }

  ≼-trans-assoc : {α : N u} {α' : N v} {α'' : N w} {α''' : N w'}
    → (is : α ≼ α') (is' : α' ≼ α'') (is'' : α'' ≼ α''')
    → ≼-trans (≼-trans is is') is'' ≋[≼] ≼-trans is (≼-trans is' is'')
  ≼-trans-assoc is is' is'' = ≡-refl , λ { {_} {p'''} {.p'''} ≅-refl → let
    (_ , p'' , i'') = is'' p'''
    (_ , p' , i')   = is' p''
    (_ , _ , i)     = is p'
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-assoc i i' i'') }

  -- existence of a refinement for a neighborhood that covers a specific world
  -- i.e. α ≼-⊳ v means neighborhood α has a refinement that covers world v
  _≼-⊳_ : N w → Pred W
  α ≼-⊳ v = Σ (N v) λ α' → α ≼ α'

  module _ {α : N w} {w' : W} where

    _≋[≼-⊳]_ : α ≼-⊳ w' → α ≼-⊳ w' → Set
    (α1' , is1) ≋[≼-⊳] (α2' , is2) = α1' ≡ α2' × is1 ≋[≼] is2

    ≋[≼-⊳]-refl : (x : α ≼-⊳ w') → x ≋[≼-⊳] x
    ≋[≼-⊳]-refl (α , is) = ≡-refl {x = α} , ≋[≼]-refl is

    ≋[≼-⊳]-sym : {x y : α ≼-⊳ w'} → x ≋[≼-⊳] y → y ≋[≼-⊳] x
    ≋[≼-⊳]-sym (≡-refl , is≋is') = ≡-refl , ≋[≼]-sym is≋is'

    ≋[≼-⊳]-trans : {x y z : α ≼-⊳ w'} → x ≋[≼-⊳] y → y ≋[≼-⊳] z → x ≋[≼-⊳] z
    ≋[≼-⊳]-trans (≡-refl , is≋is') (≡-refl , is'≋is'') = ≡-refl , ≋[≼]-trans is≋is' is'≋is''

  -- refinement functions
  _⇒≼_ : W → Pred W
  w ⇒≼ v = (α : N w) → α ≼-⊳ v

  -- restriction of a refinement function
  -- to the first component of its result
  _$α_ : (w ⇒≼ w') → N w → N w'
  h $α α = h α .fst

  -- restriction of a refinement function
  -- to the second component of its result
  _$≼_ : (h : w ⇒≼ w') → (α : N w) → α ≼ (h $α α)
  h $≼ α = h α .snd

  -- extensional equality for refinement functions
  _≋[⇒≼]_ : w ⇒≼ w' → w ⇒≼ w' → Set
  h ≋[⇒≼] h' = (α : N _{-w-}) → h α ≋[≼-⊳] h' α

  ≋[⇒≼]-refl : (h : w ⇒≼ w') → h ≋[⇒≼] h
  ≋[⇒≼]-refl h = λ α → ≋[≼-⊳]-refl (h α)

  ≋[⇒≼]-sym : {h h' : w ⇒≼ w'} → h ≋[⇒≼] h' → h' ≋[⇒≼] h
  ≋[⇒≼]-sym p = λ α → ≋[≼-⊳]-sym (p α)

  ≋[⇒≼]-trans : {h h' h'' : w ⇒≼ w'} → h ≋[⇒≼] h' → h' ≋[⇒≼] h'' → h ≋[⇒≼] h''
  ≋[⇒≼]-trans p q = λ α → ≋[≼-⊳]-trans (p α) (q α)

  -- (W, ⇒≼) forms a category
  ⇒≼-refl[_] : ∀ w → w ⇒≼ w
  ⇒≼-refl[ w ] = λ α → α , ≼-refl[ α ]

  ⇒≼-trans : w ⇒≼ w' → w' ⇒≼ w'' → w ⇒≼ w''
  ⇒≼-trans h h' = λ α → (h' $α (h $α α)) , ≼-trans (h $≼ α) (h' $≼ (h $α α))

  ⇒≼-trans-unit-left : (h : w ⇒≼ w') → ⇒≼-trans ⇒≼-refl[ w ] h ≋[⇒≼] h
  ⇒≼-trans-unit-left h = λ α → ≡-refl , ≼-trans-unit-left (h $≼ α)

  ⇒≼-trans-unit-right : (h : w ⇒≼ w') → ⇒≼-trans h ⇒≼-refl[ w' ] ≋[⇒≼] h
  ⇒≼-trans-unit-right h = λ α → ≡-refl , ≼-trans-unit-right (h $≼ α)

  ⇒≼-trans-assoc : (h : u ⇒≼ v) (h' : v ⇒≼ w) (h'' : w ⇒≼ w')
    → ⇒≼-trans (⇒≼-trans h h') h'' ≋[⇒≼] ⇒≼-trans h (⇒≼-trans h' h'')
  ⇒≼-trans-assoc h h' h'' = λ α
    → ≡-refl , ≼-trans-assoc (h $≼ α) (h' $≼ (h $α α)) (h'' $≼ (h' $α (h $α α) ))

  module _ (Pi : W → Pred W) (strPi : {w v v' : W} → v ⊆ v' → Pi v' w → Pi v w) where

    strForAllW : {α : N w} (i : v ⊆ v') → ForAllW α (Pi v') → ForAllW α (Pi v)
    strForAllW i fam x = strPi i (fam x)

  module _ (P : Pred W) (wkP : {w w' : W} → w ⊆ w' → P w → P w') where

    wkForAllW : {α : N w} {α' : N w'} → α ≼ α' → ForAllW α P → ForAllW α' P
    wkForAllW is fam x = let (_ , x' , i) = is x in wkP i (fam x')

  strCFam : {α : N w} (i : v ⊆ v') → ForAllW α (v' ⊆_) → ForAllW α (v ⊆_)
  strCFam i fam x = strForAllW _⊆_ ⊆-trans i fam x

  wkCFam : {α : N w} {α' : N w'} → α ≼ α' → ForAllW α (w ⊆_) → ForAllW α' (w ⊆_)
  wkCFam is fam x = wkForAllW (_ ⊆_) (flip ⊆-trans) is fam x

  record CFrame : Set₁ where

    field

      -- i.e. refine : w ⊆ w' → (α : N w) → Σ (N w') λ α' → α ≼ α'
      refine : w ⊆ w' → w ⇒≼ w'

      --
      -- refine is functorial in its first argument
      --
      refine-pres-⇒≼-refl :
          refine ⊆-refl ≋[⇒≼] ⇒≼-refl[ w ]
      refine-pres-⇒≼-trans : {w w' : W} (i : w ⊆ w') (i' : w' ⊆ w'')
        → refine (⊆-trans i i') ≋[⇒≼] ⇒≼-trans (refine i) (refine i')

    NFam : N w → Set
    NFam α = ForAllW α N

    refineNFam : {α : N w} {α' : N w'} → α ≼ α' → NFam α → NFam α'
    refineNFam is fam x = wkForAllW N (_$α_ ∘ refine) is fam x

  module _ (CF : CFrame) where

    open CFrame CF

    record Coverage : Set₁ where

      field

        -- "Covering family"
        -- Every neighbor in a neighborhood is reachable via ⊆
        cfamily : (α : N w) → ForAllW α (w ⊆_)

      field
        -- the "refinement square" commutes point-wise
        refine-comm-cfamily : (i : w ⊆ w') (α : N w)
          → ForAllW≡ _ (wkCFam (refine i $≼ α) (cfamily α)) (strCFam i (cfamily (refine i $α α)))

    -- Identity condition
    record Pointed : Set where

      field

        -- a "pointed" neighborhood
        pointN[_]     : ∀ w → N w

        -- w is a member of pointN[ w ]
        pointN-fwd-member[_]     : ∀ w → w ∈ pointN[ w ]

        -- every neighbor in pointN is an intuitionistic future of w reachable through ⊆
        pointN-bwd-reachable : ForAllW (pointN[ w ]) (w ⊆_ )

        -- coherence condition on pointed neighborhoods
        -- i.e. reaching w (as its own neighbor) via pointN-bwd-member must be through ⊆-refl
        pointN-coh[_] : ∀ w → pointN-bwd-reachable pointN-fwd-member[ w ] ≡ ⊆-refl[ w ]

      pointN-pres-≼ : w ⊆ w' → pointN[ w ] ≼ pointN[ w' ]
      pointN-pres-≼ {w} {w'} i = λ x → w , pointN-fwd-member[ w ] , ⊆-trans i (pointN-bwd-reachable x)

      -- canonical refinement of pointN[ w ] at w'
      pointN≼-⊳[_] : w ⊆ w' → pointN[ w ] ≼-⊳ w'
      pointN≼-⊳[ i ] = pointN[ _ ] , pointN-pres-≼ i

      field
        refine-coh-pointN : (i : w ⊆ w') → refine i pointN[ w ] ≋[≼-⊳] pointN≼-⊳[ i ]

    -- Transitivity condition
    record Joinable : Set₁ where

      field

        -- the neighborhoods of every neighbor (in a given neighborhood α) of w
        -- form a "joint" neighborhood of w
        joinN : (α : N w) → NFam α → N w

      ⨆_ : {α : N w} → NFam α → N w
      ⨆ α[_] = joinN _ α[_]

      field
        -- joinN preserves (setoid) equality on the second argument
        ⨆-pres-≋ : {α : N w} {α[_] : NFam α} {α[_]' : NFam α}
          → ForAllW≅ α[_] α[_]' → ⨆ α[_] ≡ ⨆ α[_]'

      -- joinN is the infinitary union
      -- c.f. https://en.wikipedia.org/wiki/Union_(set_theory)#Arbitrary_union
      field
        ⨆-bwd-member : {α : N w} (α[_] : NFam α) {v : W}
          → v ∈ (⨆ α[_]) → Exists∈ α (v ∈_ ∘ α[_])
        ⨆-fwd-member : {α : N w} (α[_] : NFam α) {v : W}
          → Exists∈ α (v ∈_ ∘ α[_]) → v ∈ (⨆ α[_])

        -- used to show that join of the cover modality preserves setoid equality
        ⨆-bwd-member-pres-≋ : {α : N w} {α[_] α[_]' : NFam α} {v : W}
          → {p : v ∈ (⨆ α[_])} {p' : v ∈ (⨆ α[_]')}
          → ForAllW≅ α[_] α[_]' → p ≅ p'
          → Exists∈≅ (⨆-bwd-member α[_] p) (⨆-bwd-member α[_]' p')
        -- Note: not used, speculative
        ⨆-fwd-member-pres-≋ : {α : N w} (α[_] α[_]' : NFam α) {v : W}
          → {p : Exists∈ α (v ∈_ ∘ α[_])} {p' : Exists∈ α (v ∈_ ∘ α[_]')}
          → ForAllW≅ α[_] α[_]' → Exists∈≅ p p'
          → ⨆-fwd-member α[_] p ≅ ⨆-fwd-member α[_]' p'

      -- join of a refined family
      ⨆'[_] : (i : w ⊆ w') {α : N w} (α[_] : NFam α) → N w'
      ⨆'[ i ] α[_] = ⨆ (refineNFam (refine i $≼ _) α[_])

      -- join of a refined family refines the joint family
      ⨆'[_]-refines : (i : w ⊆ w')
        → {α : N w} (α[_] : ForAllW α N)
        → (⨆ α[_]) ≼ (⨆'[ i ] α[_])
      ⨆'[_]-refines i α[_] {x'} p' =
        let (α'  , α≼α') = refine i _{-α-}
            (v' , v'∈α' , x'∈α[_]') = ⨆-bwd-member (refineNFam α≼α' α[_]) p'
            (v , v∈α , v⊆v') = α≼α' v'∈α'
            (α'[v'] , α[v∈α]≼α'[v'∈α']) = refine v⊆v' (α[ v∈α ])
            (x , x∈α[v∈α] , x⊆x') = α[v∈α]≼α'[v'∈α'] x'∈α[_]'
        in x , ⨆-fwd-member α[_] (v , v∈α , x∈α[v∈α]) , x⊆x'

      -- canonical refinement of joinN
      ⨆-refinement : w ⊆ w' → {α : N w} → (α[_] : NFam α) → (⨆ α[_]) ≼-⊳ w'
      ⨆-refinement i α[_] =  ⨆'[ i ] α[_] , ⨆'[ i ]-refines α[_]

      field
         refine-coh-joinN : (i : w ⊆ w') (α : N w) (α[_] : NFam α)
           → refine i (⨆ α[_]) ≋[≼-⊳] ⨆-refinement i α[_]

  module JoinableProperties (CF : CFrame) (JF : Joinable CF) where

    open CFrame CF
    open Joinable JF

    ⨆-pres-≋′ : {α α' : N w} {α[_] : NFam α} {α'[_] : NFam α'}
          → ForAllW≅ α[_] α'[_] → ⨆ α[_] ≡ ⨆ α'[_]
    ⨆-pres-≋′ (≡-refl , x) = ⨆-pres-≋ (≡-refl , x)

    ⨆-bwd-member-pres-≋′ : {α α' : N w} {α[_] : NFam α} {α'[_] : NFam α'}
          → {v : W} {p : v ∈ (⨆ α[_])} {p' : v ∈ (⨆ α'[_])}
          → ForAllW≅ α[_] α'[_] → p ≅ p'
          → Exists∈≅ (⨆-bwd-member α[_] p) (⨆-bwd-member α'[_] p')
    ⨆-bwd-member-pres-≋′ (≡-refl , x) y = ⨆-bwd-member-pres-≋ (≡-refl , x) y
