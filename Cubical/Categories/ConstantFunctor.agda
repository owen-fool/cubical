{-
  The constant functor from the unit category into a(n inhabited) category, needed for the slice category...

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.ConstantFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.UnitCategory

module ConstantFunctor {ℓ ℓ'} (𝒜 : Precategory ℓ ℓ') ⦃ 𝒜-Cat : isCategory 𝒜 ⦄ where
 

 ConstantFunctor : ∀ (A : 𝒜 .ob) → Functor UnitPrecategory 𝒜
 open Functor
 ConstantFunctor A .F-ob = λ _ → A
 ConstantFunctor A .F-hom = λ _ → 𝒜 .idn A
 ConstantFunctor A .F-idn = refl
 ConstantFunctor A .F-seq = λ _ _ → sym (𝒜 .seq-λ (𝒜 .idn A))
