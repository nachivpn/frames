{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Kripke.FDFrame.Properties {W : Set} {_⊆_ : W → W → Set} {IF : IFrame W _⊆_} {_R_ : W → W → Set}
  (let open FDF IF _R_)
  (DF : DFrame)
  (let open Definitions DF)
  where

open DFrame DF

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

--open import Relation.Binary.PropositionalEquality.Properties

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import PUtil
open import PEUtil


Reflexive-to-Serial : ReflexiveDFrame → SerialDFrame
Reflexive-to-Serial RDF = let open ReflexiveDFrame RDF in record
  { R-serial[_]           = λ w → w , R-refl[ w ]
  ; factor-pres-serial' = λ i → let (p , q , _) = Σ×-≡,≡,≡←≡ (factor-pres-R-refl i) in Σ-≡,≡→≡ (p , q)
  }


module _ (IDF : InclusiveDFrame) (SDF : SerialDFrame) where

  open InclusiveDFrame IDF
  open SerialDFrame SDF

  R-to-⊆-pres-serial : {w w' : W} (i : w ⊆ w') → ⊆-trans i (R-to-⊆ (serialR w')) ≡ ⊆-trans (R-to-⊆ (serialR w)) (serialW-pres-⊆ i)
  R-to-⊆-pres-serial {w} {w'} i = let open ≡-Reasoning ; (p , q) = Σ-≡,≡←≡ (factor-pres-serial' i) in begin
    ⊆-trans i (R-to-⊆ (serialR w'))
      ≡˘⟨ cong (⊆-trans i) (cong R-to-⊆ q) ⟩
    ⊆-trans i (R-to-⊆ (subst (w' R_) p (factorR i (serialR w))))
      ≡˘⟨ cong (⊆-trans i) (subst-application′ R-to-⊆ p) ⟩
    ⊆-trans i (subst (w' ⊆_) p (R-to-⊆ (factorR i (serialR w))))
      ≡˘⟨ subst-application′ {P = w' ⊆_} {Q = w ⊆_} (⊆-trans i) p ⟩
    subst (w ⊆_) p (⊆-trans i (R-to-⊆ (factorR i (serialR w))))
      ≡⟨ cong (subst (w ⊆_) p) (factor-pres-R-to-⊆ i (serialR w)) ⟩
    subst (w ⊆_) p (⊆-trans (R-to-⊆ (serialR w)) (factor⊆ i (serialR w)))
      ≡⟨ subst-application′ {P = serialW w ⊆_} {Q = w ⊆_} (⊆-trans (R-to-⊆ (serialR w))) p ⟩
    ⊆-trans (R-to-⊆ (serialR w)) (subst (serialW w ⊆_) p (factor⊆ i (serialR w)))
      ≡⟨⟩
    ⊆-trans (R-to-⊆ (serialR w)) (serialW-pres-⊆ i)
      ∎
