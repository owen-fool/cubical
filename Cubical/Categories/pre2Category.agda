{- 
  HoTT book excercise 9.4

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.pre2Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.IdnFunctor

record isPre2Category {ℓ ℓ'} (𝒞 : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    homIsSupSet : ∀ {x y} → isOfHLevel 3 (𝒞 .hom x y) 

open isPre2Category

module theCategories {ℓ ℓ'} where
  open Functor
  the2Category : Precategory (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  the2Category .ob = Σ (Precategory ℓ ℓ') isCategory
  the2Category .hom (𝒜 , 𝒜-Cat) (ℬ , ℬ-Cat) = Functor 𝒜 ℬ
  the2Category .idn (𝒜 , 𝒜-Cat) = γ
   where
    open IdnFunctor 𝒜 ⦃ 𝒜-Cat ⦄
    γ : Functor 𝒜 𝒜
    γ = IdnFunctor
  the2Category .seq f g .F-ob A = g .F-ob (f .F-ob A)
  the2Category .seq f g .F-hom H = g .F-hom (f .F-hom H)
  the2Category .seq f g .F-idn = cong (λ - → g .F-hom -) (f .F-idn) ∙ g .F-idn
  the2Category .seq f g .F-seq H H' = (cong (λ - → g .F-hom -) (f .F-seq H H')) ∙ g .F-seq (F-hom f H) (F-hom f H')
  the2Category .seq-λ F i .F-ob = {!!}
  the2Category .seq-λ F i .F-hom = {!!}
  the2Category .seq-λ F i .F-idn = {!!}
  the2Category .seq-λ F i .F-seq = {!!}
  the2Category .seq-ρ = {!!}
  the2Category .seq-α = {!!}
