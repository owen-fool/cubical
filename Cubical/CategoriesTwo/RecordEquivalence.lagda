Proving the equivalence between categories defined as records and categories defined as sigmas

\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.RecordEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.CategoriesTwo.Category renaming (homIsSet to homSet)
open import Cubical.Categories.Category

Canon : {ℓ ℓ' : Level} → Precategory ℓ ℓ' → UrPreCategory ℓ ℓ'
Canon 𝒞 = (𝒞 .ob) , ((𝒞 .hom) , ((𝒞 .idn) , ((𝒞 .seq) ,
                      (𝒞 .seq-α) , ((𝒞 .seq-λ) , (𝒞 .seq-ρ)))))

Canon' : {ℓ ℓ' : Level} → Σ (Precategory ℓ ℓ') (λ 𝒞 → isCategory 𝒞) → PreCategory ℓ ℓ'
Canon' (𝒞 , isCat-𝒞) = 𝒪𝒷 ⟪ Canon 𝒞 ⟫' , (snd ⟪ Canon 𝒞 ⟫' ,
                       (isCat-𝒞 .homIsSet , (((𝒞 .seq-λ) , (𝒞 .seq-ρ)) , 𝒞 .seq-α)))

Canon'⁻¹ : {ℓ ℓ' : Level} → PreCategory ℓ ℓ' → Σ (Precategory ℓ ℓ') (λ 𝒞 → isCategory 𝒞)
fst (Canon'⁻¹ 𝓒) .ob = 𝒪𝒷 ⟪ 𝓒 ⟫
fst (Canon'⁻¹ 𝓒) .hom = 𝒽 ⟪ 𝓒 ⟫
fst (Canon'⁻¹ 𝓒) .idn = 𝒾𝒹⟦ 𝓒 ⟧
fst (Canon'⁻¹ 𝓒) .seq = 𝑆⟦ 𝓒 ⟧
fst (Canon'⁻¹ 𝓒) .seq-λ = 𝑆-λ⟦ 𝓒 ⟧
fst (Canon'⁻¹ 𝓒) .seq-ρ = 𝑆-ρ⟦ 𝓒 ⟧
fst (Canon'⁻¹ 𝓒) .seq-α = 𝑆-α⟦ 𝓒 ⟧
snd (Canon'⁻¹ 𝓒) .homIsSet = 𝒽-sets⟦ 𝓒 ⟧

sectionCanon' : {ℓ ℓ' : Level} → section (Canon' {ℓ} {ℓ'}) Canon'⁻¹
sectionCanon' 𝓒 = refl

retractCanon' : {ℓ ℓ' : Level} → retract (Canon' {ℓ} {ℓ'}) Canon'⁻¹
fst (retractCanon' (𝒞 , isCat-𝒞) i) .ob = 𝒞 .ob
fst (retractCanon' (𝒞 , isCat-𝒞) i) .hom = 𝒞 .hom
fst (retractCanon' (𝒞 , isCat-𝒞) i) .idn = 𝒞 .idn
fst (retractCanon' (𝒞 , isCat-𝒞) i) .seq = 𝒞 .seq
fst (retractCanon' (𝒞 , isCat-𝒞) i) .seq-λ = 𝒞 .seq-λ
fst (retractCanon' (𝒞 , isCat-𝒞) i) .seq-ρ = 𝒞 .seq-ρ
fst (retractCanon' (𝒞 , isCat-𝒞) i) .seq-α = 𝒞 .seq-α
snd (retractCanon' (𝒞 , isCat-𝒞) i) .homIsSet = isCat-𝒞 .homIsSet

EquivWhenHomsSets : {ℓ ℓ' : Level} → isEquiv (Canon' {ℓ} {ℓ'})
EquivWhenHomsSets = isoToIsEquiv (iso Canon' Canon'⁻¹ sectionCanon' retractCanon')

ΣPrecat,homIsSet≡PreCat : (ℓ ℓ' : Level)
                       → Σ (Precategory ℓ ℓ') (λ 𝒞 → isCategory 𝒞) ≡ PreCategory ℓ ℓ'
ΣPrecat,homIsSet≡PreCat ℓ ℓ' = ua (Canon' , EquivWhenHomsSets)
\end{code}
