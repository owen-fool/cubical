{- 
  Characterising equality of category isomorphisms

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.CatIsoEquality where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module CatIsoEquality {ℓ ℓ'} (𝒜 : Precategory ℓ ℓ') ⦃ 𝒜-Cat : isCategory 𝒜 ⦄ ⦃ 𝒜-Univ : isUnivalent 𝒜 ⦄ where
 open CatIso {ℓ} {ℓ'} {𝒜}

 CatIsoEquality : (x y : 𝒜 .ob) → (I I' : CatIso x y) → (p : I .h ≡ I' .h) → (q : I .h⁻¹ ≡ I' .h⁻¹)
               → I .sec ≡ transport (cong (λ - → (𝒜 .seq - (I' .h) ≡ 𝒜 .idn y)) (sym q) ∙ cong (λ - → (𝒜 .seq (I .h⁻¹) - ≡ 𝒜 .idn y)) (sym p)) (I' .sec)
               → I .ret ≡ transport ((cong (λ - → (𝒜 .seq - (I' .h⁻¹) ≡ 𝒜 .idn x)) (sym p)) ∙ cong (λ - → (𝒜 .seq (I .h) - ≡ 𝒜 .idn x)) (sym q)) (I' .ret) → I ≡ I
 CatIsoEquality x y I₁ I' p q x₁ x₂ = refl

