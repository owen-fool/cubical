{- 
  The identity functor, from a category to itself, needed for the slice category...

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.IdnFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

module IdnFunctor {ℓ ℓ'} (𝒜 : Precategory ℓ ℓ') ⦃ 𝒜-Cat : isCategory 𝒜 ⦄ where
 open Functor

 IdnFunctor : Functor 𝒜 𝒜
 IdnFunctor .F-ob = λ A → A
 IdnFunctor .F-hom = λ f → f
 IdnFunctor .F-idn = refl
 IdnFunctor .F-seq = λ f g → refl
