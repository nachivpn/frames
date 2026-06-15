{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.FDFrame as FDF

module Frame.FDFrame.Properties {W : Set} {_⊑_ : W → W → Set} {IF : IFrame W _⊑_} {_R_ : W → W → Set}
  (let open FDF IF _R_)
  (DF : DFrame)
  (let open Definitions DF)
  where

open DFrame DF

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import PUtil

∙-assoc : {w w' v' v : W} (i : w ⊑ w') (d : w D v') (i' : v ⊑ v') → (i ᵢ∙ d) ∙ᵢ i' ≡ i ᵢ∙ (d ∙ᵢ i')
∙-assoc i d i' = Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ≡-sym (⊑-trans-assoc _ _ _))

∙ᵢ-pres-⊑-refl : {w v : W} → (d : w D v) → d ∙ᵢ ⊑-refl ≡ d
∙ᵢ-pres-⊑-refl d = Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊑-trans-unit-left (wit⊑ d))

ᵢ∙-pres-⊑-refl : {w v : W} → (d : w D v) → ⊑-refl ᵢ∙ d ≡ d
ᵢ∙-pres-⊑-refl d rewrite factor-pres-⊑-refl (witR d) = Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊑-trans-unit-right (wit⊑ d))

∙ᵢ-pres-⊑-trans : {w v v' v'' : W} (d : w D v'') (i : v' ⊑ v'') (i' : v ⊑ v')
  → d ∙ᵢ (⊑-trans i' i) ≡ (d ∙ᵢ i) ∙ᵢ i'
∙ᵢ-pres-⊑-trans d i i' = Σ×-≡,≡,≡→≡ (≡-refl , (≡-refl , (⊑-trans-assoc _ _ _)))

ᵢ∙-pres-⊑-trans : {w w' w'' v : W} (i : w ⊑ w') (i' : w' ⊑ w'') (d : w D v)
  → (⊑-trans i i') ᵢ∙ d ≡ i' ᵢ∙ (i ᵢ∙ d)
ᵢ∙-pres-⊑-trans i i' d rewrite factor-pres-⊑-trans i i' (witR d) = Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ≡-sym (⊑-trans-assoc _ _ _))

open import Frame.BFrame IF _D_

D-is-bimodule : BFrame
D-is-bimodule = record
  { _ᵢ∙_            = _ᵢ∙_
  ; _∙ᵢ_            = _∙ᵢ_
  ; ∙-assoc         = ∙-assoc
  ; ᵢ∙-pres-⊑-refl  = ᵢ∙-pres-⊑-refl
  ; ∙ᵢ-pres-⊑-refl  = ∙ᵢ-pres-⊑-refl
  ; ᵢ∙-pres-⊑-trans = ᵢ∙-pres-⊑-trans
  ; ∙ᵢ-pres-⊑-trans = ∙ᵢ-pres-⊑-trans
  }
