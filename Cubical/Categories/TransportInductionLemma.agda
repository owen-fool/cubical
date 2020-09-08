{- 
  of uncertain veracity:
  ∀ g : hom X B, ∀ k : X ≡ X', transport (λ -, hom - B) k g ≡ f ∘ g
  where we are in a category so that k ≈ f ∘ f⁻¹ ≡ id etc.
-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.TransportInductionLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Categories.Category

module TransportInductionLemma {ℓ ℓ'} (𝒜 : Precategory ℓ ℓ') ⦃ 𝒜-Cat : isCategory 𝒜 ⦄ ⦃ 𝒜-Univ : isUnivalent 𝒜 ⦄ where
 open Iso
 open CatIso
 

 TransportInductionLemma : (X X' B : 𝒜 .ob) (p : X ≡ X') (g : 𝒜 .hom X B)
                         → transport (cong (λ x → 𝒜 .hom x B) p) g ≡ 𝒜 .seq (((invIso (equivToIso ((pathToIso X X') , (𝒜-Univ .univ X X')))) .inv p) .h⁻¹) g
 TransportInductionLemma X X' B p g =
  J (λ y q → transport (cong (λ x → 𝒜 .hom x B) q) g ≡ 𝒜 .seq ((invIso (equivToIso ((pathToIso X y) , (𝒜-Univ .univ X y))) .inv q) .h⁻¹) g) (sym (cong (λ - → 𝒜 .seq - g)
    (transportRefl (idn 𝒜 X)) ∙ (𝒜 .seq-λ g ∙ (sym (transportRefl g))))) p

