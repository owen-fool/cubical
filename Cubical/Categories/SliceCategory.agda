{- 
  HoTT book Excercise 9.1

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.SliceCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.CommaCategory
open import Cubical.Categories.ConstantFunctor
open import Cubical.Categories.IdnFunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.TransportInductionLemma
open import Cubical.Categories.UnitCategory
open import Cubical.Core.Glue
open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism


module SliceCategory {ℓ ℓ'} (𝒜 : Precategory ℓ ℓ') ⦃ 𝒜-Cat : isCategory 𝒜 ⦄ where
 open CommaCategory 𝒜 UnitPrecategory 𝒜 ⦃ 𝒜-Cat ⦄ ⦃ UnitCategory ⦄ ⦃ 𝒜-Cat ⦄
 open IdnFunctor 𝒜
 open ConstantFunctor 𝒜
 open Iso
 open CatIso
 

 SliceCategory : ∀ (A : 𝒜 .ob) → Precategory (ℓ-max (ℓ-max ℓ' ℓ-zero) ℓ) (ℓ-max (ℓ-max ℓ' ℓ-zero) ℓ')
 SliceCategory A = CommaCategory IdnFunctor (ConstantFunctor A)

 UnivalentCondition : ∀ (A : 𝒜 .ob) → isUnivalent 𝒜 → isUnivalent (SliceCategory A)
 UnivalentCondition A 𝒜-univ .univ (𝐴 , tt , h) (𝐴' , tt , h') = isoToIsEquiv (iso (pathToIso (𝐴 , tt , h) (𝐴' , tt , h')) {!!} {!!} {!!})
  where
   open TransportInductionLemma 𝒜 ⦃ 𝒜-Cat ⦄ ⦃ 𝒜-univ ⦄


 
