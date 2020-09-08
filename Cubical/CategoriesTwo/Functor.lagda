\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.Functor where

open import Cubical.Foundations.Prelude
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
