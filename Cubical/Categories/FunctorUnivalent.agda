{- 
  Failed to prove this in one species of HoTT, lets try this in Agda

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.FunctorUnivalent where

open import Cubical.Core.Glue
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.CatIsoEquality
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

module _ {ℓ ℓ' 𝒍 𝒍'} (𝒞 : Precategory ℓ ℓ') ⦃ 𝒞-Cat : isCategory 𝒞 ⦄
         (𝒟 : Precategory 𝒍 𝒍') ⦃ 𝒟-Cat : isCategory 𝒟 ⦄ ⦃ 𝒟-Univ : isUnivalent 𝒟 ⦄ where
 open Precategory
 open NatTrans
 open Functor
 open CatIsoEquality

 Auxiliary : (F G : FUNCTOR 𝒞 𝒟 .ob)
          → CatIso {ℓ-max (ℓ-max (ℓ-max ℓ ℓ') 𝒍) 𝒍'}
                    {ℓ-max (ℓ-max ℓ ℓ') (ℓ-max 𝒍 𝒍')}
                    {FUNCTOR 𝒞 𝒟} F G
          → F ≡ G
 Auxiliary F G (catiso h h⁻¹ sec ret) = {!!}

 FunctorUnivalent : isUnivalent (FUNCTOR 𝒞 𝒟) 
 FunctorUnivalent .univ F G = isoToIsEquiv (iso {!!} {!!} {!!} {!!})
