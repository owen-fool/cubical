\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.NatTransCatIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.CategoriesTwo.Category
open import Cubical.CategoriesTwo.Functor
open import Cubical.CategoriesTwo.NaturalTransformation

NatTransIsoLeft : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
                  (F G : 𝒪𝒷 ⟪ FUNCTOR 𝓒 𝓓 ⟫) (x : 𝒪𝒷 ⟪ 𝓒 ⟫)
               → CatIso ⟪ FUNCTOR 𝓒 𝓓 ⟫ F G
               → CatIso ⟪ 𝓓 ⟫ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)
NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , sec , ret) =
 (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x) , (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ F ⟩ δ ] x) ,
 (funExt⁻ (λ i → fst (sec i)) x) , funExt⁻ (λ i → fst (ret i)) x


isotoid : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
       → isUniv 𝓓 → (F G : 𝒪𝒷 ⟪ (FUNCTOR 𝓒 𝓓) ⟫) → CatIso ⟪ FUNCTOR 𝓒 𝓓 ⟫ F G → F ≡ G
isotoid 𝓒 𝓓 isUniv-𝓓 F G (γ , δ , p , q) =
 ΣPathP ((funExt λ x →
  Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
  (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q))) ,
 ΣPathP
  (implicitFunExt (λ {x} → implicitFunExt (λ {y} → funExt (λ f →
   toPathP ((transIsoNeutral 𝓓 _ _ _ _
            (Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
  (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)))
  (Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)))
  (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q))) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f)) ∙
  (cong (λ - → 𝑆⟦ 𝓓 ⟧ ←[⟦ 𝓓 ⟧⟨ 𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x ⟩⟨ 𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x ⟩
    idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)
    (Iso.inv
     (equivToIso
      (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
       isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
     (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)))
    ] (𝑆⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) -))
    (λ i → fst (Iso.rightInv (equivToIso (idtoiso 𝓓 (fst F y) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)))
    (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q)) i1) , isUniv-𝓓 (fst F y) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)))
    (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q)) i1)))
    (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q)) i)) ∙
    cong (λ - → 𝑆⟦ 𝓓 ⟧ - (𝑆⟦ 𝓓 ⟧ (fst (snd F) f) (fst γ y)))
    λ i → fst (snd (Iso.rightInv (equivToIso (idtoiso 𝓓 (fst F x) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
    (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)) i1) , isUniv-𝓓 (fst F x) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
    (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)) i1)))
    (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)) i))) ∙
    (cong (𝑆⟦ 𝓓 ⟧ (fst δ x)) (γ-nat[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x y f)) ∙
    (sym (𝑆-α⟦ 𝓓 ⟧ (fst δ x) (fst γ x) (fst (snd G) f))) ∙
    (cong (λ - → 𝑆⟦ 𝓓 ⟧ - (fst (snd G) f)) (funExt⁻ (λ i → fst (p i)) x)) ∙
    𝑆-λ⟦ 𝓓 ⟧ (fst (snd G) f))))) ,
    toPathP (isProp×
    (isPropImplicitΠ (λ x → 𝒽-sets⟦ 𝓓 ⟧ _ _))
    (isPropImplicitΠ (λ x →
     isPropImplicitΠ (λ y → isPropImplicitΠ (λ z →
     isPropΠ (λ f → isPropΠ (λ g → 𝒽-sets⟦ 𝓓 ⟧ _ _)))))) _ _)))
 

UnivEquiv : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
         → isUniv 𝓓 → isUniv (FUNCTOR 𝓒 𝓓)
UnivEquiv 𝓒 𝓓 isUniv-𝓓 F G =
 isoToIsEquiv (iso (idtoiso (FUNCTOR 𝓒 𝓓) F G) (isotoid 𝓒 𝓓 isUniv-𝓓 F G)
 {!!} {!!})
\end{code}
