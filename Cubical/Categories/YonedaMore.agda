{- 
  Some lemmas in the section of the HoTT book following on from the Yoneda Lemma

-}

{-# OPTIONS --cubical --no-import-sorts --postfix-projections --safe #-}

module Cubical.Categories.YonedaMore where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaves

module _ {ℓ} (𝒞 : Precategory ℓ ℓ) ⦃ 𝒞-Cat : isCategory 𝒞 ⦄ ⦃ 𝒞-Univ : isUnivalent 𝒞 ⦄ where
 open Yoneda 𝒞 ⦃ 𝒞-Cat ⦄

 yoEmbedding : ∀ x y → yo x ≡ yo y → x ≡ y
 yoEmbedding = {!!}
