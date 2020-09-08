{-
  Definition of the unit category, 𝟏, which is needed for defining the slice category...

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.UnitCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Data.Prod
open import Cubical.Data.Unit

UnitPrecategory : Precategory ℓ-zero ℓ-zero
UnitPrecategory .ob = Unit
UnitPrecategory .hom = λ _ _ → Unit
UnitPrecategory .idn = λ _ → tt
UnitPrecategory .seq = λ _ _ → tt
UnitPrecategory .seq-λ = λ _ → refl
UnitPrecategory .seq-ρ = λ _ → refl
UnitPrecategory .seq-α = λ _ _ _ → refl

UnitCategory : isCategory UnitPrecategory
UnitCategory .homIsSet = isSetUnit


