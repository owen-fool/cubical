\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.CategoriesTwo.Category

Functor : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
       → Type (ℓ-max (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟) ℓ𝒟')
Functor 𝓒 𝓓 =
 Σ (𝒪𝒷 ⟪ 𝓒 ⟫ → 𝒪𝒷 ⟪ 𝓓 ⟫)
   λ F → Σ ({x y : 𝒪𝒷 ⟪ 𝓒 ⟫} → 𝒽 ⟪ 𝓒 ⟫ x y → 𝒽 ⟪ 𝓓 ⟫ (F x) (F y))
            λ 𝑭 → (∀ {x} → 𝑭 (𝒾𝒹⟦ 𝓒 ⟧ x) ≡ 𝒾𝒹⟦ 𝓓 ⟧ (F x))
                 × (∀ {x y z} (f : 𝒽 ⟪ 𝓒 ⟫ x y) (g : 𝒽 ⟪ 𝓒 ⟫ y z)
                    → 𝑭 (𝑆⟦ 𝓒 ⟧ f g) ≡ 𝑆⟦ 𝓓 ⟧ (𝑭 f) (𝑭 g))
\end{code}

Some projections

\begin{code}
𝐹[⟦_⟧⟦_⟧_] : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
       (F : Functor 𝓒 𝓓) → 𝒪𝒷 ⟪ 𝓒 ⟫ → 𝒪𝒷 ⟪ 𝓓 ⟫
𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ 𝐹 , 𝑭 , _ ] = 𝐹

𝑭[⟦_⟧⟦_⟧_] : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
              (F : Functor 𝓒 𝓓) → {x y : 𝒪𝒷 ⟪ 𝓒 ⟫} → 𝒽 ⟪ 𝓒 ⟫ x y
              → 𝒽 ⟪ 𝓓 ⟫ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y)
𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ 𝐹 , 𝑭 , _ ] = 𝑭

𝑭-ι[⟦_⟧⟦_⟧_] : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
                (F : Functor 𝓒 𝓓) {x : 𝒪𝒷 ⟪ 𝓒 ⟫}
             → 𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] (𝒾𝒹⟦ 𝓒 ⟧ x) ≡ 𝒾𝒹⟦ 𝓓 ⟧ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x)
𝑭-ι[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ 𝐹 , 𝑭 , ι , _ ] = ι

𝑭-σ[⟦_⟧⟦_⟧_] : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
                (F : Functor 𝓒 𝓓) → {x y z : 𝒪𝒷 ⟪ 𝓒 ⟫} (f : 𝒽 ⟪ 𝓒 ⟫ x y) (g : 𝒽 ⟪ 𝓒 ⟫ y z)
                → 𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] (𝑆⟦ 𝓒 ⟧ f g)
                 ≡ 𝑆⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] g)
𝑭-σ[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ 𝐹 , 𝑭 , _ , σ ] = σ
\end{code}

Functors may have properties

\begin{code}
is-full : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
          (F : Functor 𝓒 𝓓) → Type (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟')
is-full 𝓒 𝓓 F = ∀ x y (F[f] : 𝒽 ⟪ 𝓓 ⟫ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y))
               → ∃ (𝒽 ⟪ 𝓒 ⟫ x y) (λ f → 𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f ≡ F[f])

is-faithful : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
              (F : Functor 𝓒 𝓓) → Type (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟')
is-faithful 𝓒 𝓓 F = ∀ x y (f g : 𝒽 ⟪ 𝓒 ⟫ x y)
                   → 𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f ≡ 𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] g → f ≡ g
\end{code}

For Isomorphism proofs

\begin{code}

FunctorIdenLemma : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
                   (F G : Functor 𝓒 𝓓) (p : F ≡ G) (p' : fst F ≡ fst G)
                 → p' ≡ (λ i → (fst (p i))) →
                   (q' : PathP
                           (λ i →
                              Σ ({x y : 𝒪𝒷 ⟪ 𝓒 ⟫} → 𝒽 ⟪ 𝓒 ⟫ x y → 𝒽 ⟪ 𝓓 ⟫ (p' i x) (p' i y))
                              (λ 𝑭 →
                                 ({x : 𝒪𝒷 ⟪ 𝓒 ⟫} → 𝑭 (𝒾𝒹⟦ 𝓒 ⟧ x) ≡ 𝒾𝒹⟦ 𝓓 ⟧ (p' i x)) ×
                                 ({x y z : 𝒪𝒷 ⟪ 𝓒 ⟫} (f : 𝒽 ⟪ 𝓒 ⟫ x y) (g : 𝒽 ⟪ 𝓒 ⟫ y z) →
                                  𝑭 (𝑆⟦ 𝓒 ⟧ f g) ≡ 𝑆⟦ 𝓓 ⟧ (𝑭 f) (𝑭 g))))
                           (snd F) (snd G))
                → ΣPathP (p' , q') ≡ p
FunctorIdenLemma {ℓ𝒞} {ℓ𝒞'} {ℓ𝒟} {ℓ𝒟'} 𝓒 𝓓 F G p p' p'≡fstp q' =
 (cong ΣPathP (Σ≡Prop (λ - → isOfHLevelPathP' {ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟'} {(λ i →
             Σ ({x y : 𝒪𝒷 ⟪ 𝓒 ⟫} → 𝒽 ⟪ 𝓒 ⟫ x y → 𝒽 ⟪ 𝓓 ⟫ (- i x) (- i y))
             (λ 𝑭 →
                ({x : 𝒪𝒷 ⟪ 𝓒 ⟫} → 𝑭 (𝒾𝒹⟦ 𝓒 ⟧ x) ≡ 𝒾𝒹⟦ 𝓓 ⟧ (- i x)) ×
                ({x y z : 𝒪𝒷 ⟪ 𝓒 ⟫} (f : 𝒽 ⟪ 𝓒 ⟫ x y) (g : 𝒽 ⟪ 𝓒 ⟫ y z) →
                 𝑭 (𝑆⟦ 𝓒 ⟧ f g) ≡ 𝑆⟦ 𝓓 ⟧ (𝑭 f) (𝑭 g))))} 1
 (λ x y → isSetΣ (isSetImplicitΠ (λ x → isSetImplicitΠ (λ y → isSetΠ (λ f → 𝒽-sets⟦ 𝓓 ⟧)))) (λ 𝑯 → isSet× (isSetImplicitΠ (λ x → isProp→isSet (𝒽-sets⟦ 𝓓 ⟧ (𝑯 (𝒾𝒹⟦ 𝓒 ⟧ x)) (𝒾𝒹⟦ 𝓓 ⟧ (- i1 x))))) (isSetImplicitΠ (λ x → isSetImplicitΠ (λ y → isSetImplicitΠ (λ z → isSetΠ (λ f → isSetΠ (λ g → isProp→isSet (𝒽-sets⟦ 𝓓 ⟧ (𝑯 (𝑆⟦ 𝓒 ⟧ f g)) (𝑆⟦ 𝓓 ⟧ (𝑯 f) (𝑯 g)))))))))) x y) (snd F) (snd G)) p'≡fstp)) ∙ refl
 
  

\end{code}
