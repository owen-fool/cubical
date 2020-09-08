{-
  Definition of the comma category. 
  This is as found at https://en.wikipedia.org/wiki/Comma_category 

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.CommaCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Sigma

module CommaCategory { ℓ𝒜 ℓ𝒜' ℓℬ ℓℬ' ℓ𝒞 ℓ𝒞' } ( 𝒜 : Precategory ℓ𝒜 ℓ𝒜' ) ( ℬ : Precategory ℓℬ ℓℬ' ) ( 𝒞 : Precategory ℓ𝒞 ℓ𝒞' )
                     ⦃ 𝒜-Cat : isCategory 𝒜 ⦄ ⦃ ℬ-Cat : isCategory ℬ ⦄ ⦃ 𝒞-Cat : isCategory 𝒞 ⦄ where
 open Functor

 {- Given three categories, 𝒜, ℬ and 𝒞, and two functors, 𝒮 : 𝒜 → 𝒞, 𝒯 : ℬ → 𝒞, we can form the comma category, (𝒮↓𝒯).
    The objects of the comma category are triples, (A , B , h) where A is an object of 𝒜, B is an object of ℬ and h is a morphism
    in 𝒞 from 𝒮(A) to 𝒯(B).
    The morphisms (for objects (A , B , h), (A' , B' , h')) of the comma category are pairs of morphisms (f , g), f : A → A', g : B → B',
    together with a proof that the following diagram commutes:
    
           𝒮(f)
    𝒮(A) ───────⟩ 𝒮(A')
     |              |
     |              |
   h |              | h'     ---downwards dashing unintentional!
     |              |
     ↓              ↓
    𝒯(B) ───────⟩ 𝒯(B')
            𝒯(g)

    Composition and identity are defined in the standard way for pairs of morphisms.
 
 -}

 CommaCategory : (𝒮 : Functor 𝒜 𝒞) (𝒯 : Functor ℬ 𝒞) → Precategory (ℓ-max (ℓ-max ℓ𝒞' ℓℬ) ℓ𝒜) (ℓ-max (ℓ-max ℓ𝒜' ℓℬ') ℓ𝒞')
 CommaCategory 𝒮 𝒯 .ob = Σ (𝒜 .ob) (λ A → Σ (ℬ .ob) (λ B → 𝒞 .hom (𝒮 .F-ob A) (𝒯 .F-ob B)))
 CommaCategory 𝒮 𝒯 .hom (A , B , h) (A' , B' , h') = Σ (𝒜 .hom A A') (λ f → Σ (ℬ .hom B B') (λ g → 𝒞 .seq (𝒮 .F-hom f) h' ≡ 𝒞 .seq h (𝒯 .F-hom g)))
 CommaCategory 𝒮 𝒯 .idn (A , B , h) = (𝒜 .idn A) , ((ℬ .idn B) , (cong (λ 𝔥 → 𝒞 .seq 𝔥 h) (𝒮 .F-idn)) ∙ (𝒞 .seq-λ h) ∙ (sym ((cong (λ 𝔥 → 𝒞 .seq h 𝔥) (𝒯 .F-idn)) ∙ (𝒞 .seq-ρ h))))
 CommaCategory 𝒮 𝒯 .seq (f , g , p) (f' , g' , q) = (𝒜 .seq f f') , ((ℬ .seq g g') , cong (λ 𝔥 → 𝒞 .seq 𝔥 _) (𝒮 .F-seq f f') ∙ (𝒞 .seq-α _ _ _)
                                                                                        ∙ (cong (λ 𝔥 → 𝒞 .seq (𝒮 .F-hom f) 𝔥) q) ∙ (sym (𝒞 .seq-α _ _ _))
                                                                                        ∙ (cong (λ 𝔥 → 𝒞 .seq 𝔥 (𝒯 .F-hom g')) p) ∙ (𝒞 .seq-α _ _ _) ∙ cong (λ 𝔥 → 𝒞 .seq _ 𝔥) (sym (𝒯 .F-seq _ _)))
 CommaCategory 𝒮 𝒯 .seq-λ (f , g , p) = ΣPathP ((𝒜 .seq-λ f) , ΣPathP ((ℬ .seq-λ g) , toPathP (𝒞-Cat .homIsSet _ _ _ _)))
 CommaCategory 𝒮 𝒯 .seq-ρ (f , g , p) = ΣPathP ((𝒜 .seq-ρ f) , (ΣPathP ((ℬ .seq-ρ g) , toPathP (𝒞-Cat .homIsSet _ _ _ _))))
 CommaCategory 𝒮 𝒯 .seq-α (f , g , p) (f' , g' , p') (𝑓 , 𝑔 , 𝑝) = ΣPathP ((𝒜 .seq-α _ _ _) , ΣPathP ((ℬ .seq-α _ _ _) , toPathP (𝒞-Cat .homIsSet _ _ _ _)))
