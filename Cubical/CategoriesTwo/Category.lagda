\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.Category where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms

homType : (ℓ ℓ' : Level) (ob : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
homType ℓ ℓ' ob = ob → ob → Type ℓ'

idnType : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob) → Type (ℓ-max ℓ ℓ')
idnType ℓ ℓ' ob hom = ∀ x → hom x x

seqType : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob) → Type (ℓ-max ℓ ℓ')
seqType ℓ ℓ' ob hom = ∀ {x y z} (f : hom x y) (g : hom y z) → hom x z

seq-λType : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
            (idn : idnType ℓ ℓ' ob hom) (seq : seqType ℓ ℓ' ob hom)
         → Type (ℓ-max ℓ ℓ')
seq-λType ℓ ℓ' ob hom idn seq = ∀ {x y} (f : hom x y) → seq (idn x) f ≡ f

seq-ρType : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
            (idn : idnType ℓ ℓ' ob hom) (seq : seqType ℓ ℓ' ob hom)
         → Type (ℓ-max ℓ ℓ')
seq-ρType ℓ ℓ' ob hom idn seq = ∀ {x y} (f : hom x y) → seq f (idn y) ≡ f

seq-αType : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
            (seq : seqType ℓ ℓ' ob hom)
         → Type (ℓ-max ℓ ℓ')
seq-αType ℓ ℓ' ob hom seq =
 ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) → seq (seq f g) h ≡ seq f (seq g h)

CategoryStructure : {ℓ ℓ' : Level} (ob : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
CategoryStructure {ℓ} {ℓ'} ob = 
                    Σ (homType ℓ ℓ' ob)
                      (λ hom → Σ (idnType ℓ ℓ' ob hom)
                                  (λ idn → (seqType ℓ ℓ' ob hom)))

TypeValuedPreOrder : (ℓ ℓ' : Level) →  Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
TypeValuedPreOrder ℓ ℓ' = TypeWithStr ℓ (CategoryStructure {ℓ} {ℓ'})
\end{code}

Some (not-so-)useful projections

\begin{code}

𝒪𝒷 : {ℓ ℓ' : Level} (𝒞 : TypeValuedPreOrder ℓ ℓ') → Type ℓ
𝒪𝒷 {ℓ} {ℓ'} (ob , hom , idn , seq) = ob

𝒽 : {ℓ ℓ' : Level} (𝒞 : TypeValuedPreOrder ℓ ℓ') → 𝒪𝒷 𝒞 → 𝒪𝒷 𝒞 → Type ℓ'
𝒽 (ob , hom , idn , seq) = hom

𝒾𝒹 : {ℓ ℓ' : Level} {𝒞 : TypeValuedPreOrder ℓ ℓ'} → (x : 𝒪𝒷 𝒞) → 𝒽 𝒞 x x
𝒾𝒹 {ℓ} {ℓ'} {ob , hom , idn , seq} = idn

_◒_ : {ℓ ℓ' : Level} {𝒞 : TypeValuedPreOrder ℓ ℓ'} → {x y z : 𝒪𝒷 𝒞} →
       𝒽 𝒞 x y → 𝒽 𝒞 y z → 𝒽 𝒞 x z
_◒_ {ℓ} {ℓ'} {ob , hom , idn , seq} {x} {y} {z} = seq {x} {y} {z}
\end{code}

New section on the category axioms, ideally complete with proofs that these axioms are prop-sized

\begin{code}
homIsSet : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob) → Type (ℓ-max ℓ ℓ')
homIsSet ℓ ℓ' ob hom = ∀ {x y} → isSet (hom x y)

homIsSetIsProp : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
              → isProp (homIsSet ℓ ℓ' ob hom)
homIsSetIsProp ℓ ℓ' ob hom = isPropImplicitΠ λ x → isPropImplicitΠ (λ y → isPropIsSet)

seq-λTypeIsProp : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
                  (idn : idnType ℓ ℓ' ob hom) (seq : seqType ℓ ℓ' ob hom)
                  (homSets : homIsSet ℓ ℓ' ob hom)
                → isProp (seq-λType ℓ ℓ' ob hom idn seq)
seq-λTypeIsProp ℓ ℓ' ob hom idn seq homSets =
 isPropImplicitΠ λ x → isPropImplicitΠ (λ y → isPropΠ (λ f → homSets (seq (idn x) f) f))

seq-ρTypeIsProp : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
                  (idn : idnType ℓ ℓ' ob hom) (seq : seqType ℓ ℓ' ob hom)
                  (homSets : homIsSet ℓ ℓ' ob hom)
                → isProp (seq-ρType ℓ ℓ' ob hom idn seq)
seq-ρTypeIsProp ℓ ℓ' ob hom idn seq homSets =
 isPropImplicitΠ λ x → isPropImplicitΠ (λ y → isPropΠ (λ f → homSets (seq f (idn y)) f))

seq-αTypeIsProp : (ℓ ℓ' : Level) (ob : Type ℓ) (hom : homType ℓ ℓ' ob)
                  (idn : idnType ℓ ℓ' ob hom) (seq : seqType ℓ ℓ' ob hom)
                  (homSets : homIsSet ℓ ℓ' ob hom)
                → isProp (seq-αType ℓ ℓ' ob hom seq)
seq-αTypeIsProp ℓ ℓ' ob hom idn seq homSets =
 isPropImplicitΠ λ w →
  isPropImplicitΠ (λ x →
   isPropImplicitΠ λ y →
    isPropImplicitΠ (λ z →
     isPropΠ (λ f →
      isPropΠ (λ g →
       isPropΠ (λ h → homSets (seq (seq f g) h) (seq f (seq g h)))))))

satCategoryAx : (ℓ ℓ' : Level) (ob : Type ℓ) → CategoryStructure {ℓ} {ℓ'} ob → hProp (ℓ-max ℓ ℓ')
satCategoryAx ℓ ℓ' ob (hom , idn , seq) =
 (Σ (homIsSet ℓ ℓ' ob hom) λ homSets → ((seq-λType ℓ ℓ' ob hom idn seq)
                                        × seq-ρType ℓ ℓ' ob hom idn seq)
                                        × seq-αType ℓ ℓ' ob hom seq) ,
 isPropΣ (homIsSetIsProp ℓ ℓ' ob hom)
         (λ homSets → isProp× (isProp× (seq-λTypeIsProp ℓ ℓ' ob hom idn seq homSets)
                                        (seq-ρTypeIsProp ℓ ℓ' ob hom idn seq homSets))
                               (seq-αTypeIsProp ℓ ℓ' ob hom idn seq homSets))

TrueCategoryStructure : (ℓ ℓ' : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
TrueCategoryStructure ℓ ℓ' =
 AxiomsStructure (CategoryStructure {ℓ} {ℓ'}) λ ob Cat → [ satCategoryAx ℓ ℓ' ob Cat ]

PreCategory : (ℓ ℓ' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
PreCategory ℓ ℓ' = TypeWithStr ℓ (TrueCategoryStructure ℓ ℓ')
\end{code}

If i was a cleverer person, i might not need the following projections

\begin{code}
⟪_⟫ : {ℓ ℓ' : Level} → PreCategory ℓ ℓ' → TypeValuedPreOrder ℓ ℓ'
⟪ ob , (hom , idn , seq) , _ ⟫ = ob , hom , idn , seq

𝒾𝒹⟦_⟧ : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') (x : 𝒪𝒷 ⟪ 𝓒 ⟫) → 𝒽 ⟪ 𝓒 ⟫ x x
𝒾𝒹⟦ ob , (hom , idn , seq) , _ ⟧ = idn

𝑆⟦_⟧ : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') {x y z : 𝒪𝒷 ⟪ 𝓒 ⟫}
    → 𝒽 ⟪ 𝓒 ⟫ x y →  𝒽 ⟪ 𝓒 ⟫ _ z → 𝒽 ⟪ 𝓒 ⟫ _ _
𝑆⟦ ob , (hom , idn , seq) , _ ⟧ = seq

𝑆-λ⟦_⟧ : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') {x y : 𝒪𝒷 ⟪ 𝓒 ⟫}
      → (f : 𝒽 ⟪ 𝓒 ⟫ x y) → 𝑆⟦ 𝓒 ⟧ (𝒾𝒹⟦ 𝓒 ⟧ _) f ≡ f
𝑆-λ⟦ ob , (hom , idn , seq) , _ , (𝑆-λ , _) , _ ⟧ = 𝑆-λ

𝑆-ρ⟦_⟧ : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') {x y : 𝒪𝒷 ⟪ 𝓒 ⟫}
      → (f : 𝒽 ⟪ 𝓒 ⟫ x y) → 𝑆⟦ 𝓒 ⟧ f (𝒾𝒹⟦ 𝓒 ⟧ _) ≡ f
𝑆-ρ⟦ ob , (hom , idn , seq) , _ , (_ , 𝑆-ρ) , _ ⟧ = 𝑆-ρ

𝑆-α⟦_⟧ : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') {w x y z : 𝒪𝒷 ⟪ 𝓒 ⟫}
         (f : 𝒽 ⟪ 𝓒 ⟫ w x) (g : 𝒽 ⟪ 𝓒 ⟫ x y) (h : 𝒽 ⟪ 𝓒 ⟫ y z)
      → 𝑆⟦ 𝓒 ⟧ (𝑆⟦ 𝓒 ⟧ f g) h ≡ 𝑆⟦ 𝓒 ⟧ f (𝑆⟦ 𝓒 ⟧ g h)
𝑆-α⟦ ob , (hom , idn , seq) , _ , _ , 𝑆-α ⟧ = 𝑆-α

𝒽-sets⟦_⟧ : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') {x y : 𝒪𝒷 ⟪ 𝓒 ⟫}
          → isSet (𝒽 ⟪ 𝓒 ⟫ x y)
𝒽-sets⟦ ob , (hom , idn , seq) , 𝒽-sets , _ ⟧ = 𝒽-sets
\end{code}

Isomorphisms and Univalence

\begin{code}
CatIsoStructure : {ℓ ℓ' : Level} → TypeValuedPreOrder ℓ ℓ' → Type (ℓ-max ℓ ℓ')
CatIsoStructure {ℓ} {ℓ'} (ob , hom , idn , seq) = Σ ob (λ x → (Σ ob (λ y → (hom x y × hom y x))))

CatIsoSec : {ℓ ℓ' : Level} → (𝒞 : TypeValuedPreOrder ℓ ℓ') → CatIsoStructure 𝒞 → Type ℓ'
CatIsoSec {ℓ} {ℓ'} (ob , hom , idn , seq) (x , y , h , h⁻¹) =
 seq h⁻¹ h ≡ 𝒾𝒹 {ℓ} {ℓ'} {ob , hom , idn , seq} y

CatIsoRet : {ℓ ℓ' : Level} → (𝒞 : TypeValuedPreOrder ℓ ℓ') → CatIsoStructure 𝒞 → Type ℓ'
CatIsoRet {ℓ} {ℓ'} (ob , hom , idn , seq) (x , y , h , h⁻¹) =
 seq h h⁻¹ ≡ 𝒾𝒹 {ℓ} {ℓ'} {ob , hom , idn , seq} x
\end{code}

A quicker approach

\begin{code}
CatIso : {ℓ ℓ' : Level} (𝒞 : TypeValuedPreOrder ℓ ℓ') → 𝒪𝒷 𝒞 → 𝒪𝒷 𝒞 → Type ℓ'
CatIso (ob , hom , idn , seq) x y =
 Σ (hom x y) (λ h → Σ (hom y x) (λ h⁻¹ → ((seq h⁻¹ h ≡ idn y) × (seq h h⁻¹ ≡ idn x))))

CanCatIso : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') (x : 𝒪𝒷 ⟪ 𝓒 ⟫)
         → CatIso ⟪ 𝓒 ⟫ x x
CanCatIso {ℓ} {ℓ'} 𝓒 x =
 (𝒾𝒹⟦ 𝓒 ⟧ x) , (𝒾𝒹⟦ 𝓒 ⟧ x) , (𝑆-ρ⟦ 𝓒 ⟧ (𝒾𝒹⟦ 𝓒 ⟧ x)) , 𝑆-λ⟦ 𝓒 ⟧ (𝒾𝒹⟦ 𝓒 ⟧ x)

idtoiso : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') (x y : 𝒪𝒷 ⟪ 𝓒 ⟫)
       → (x ≡ y) → (CatIso ⟪ 𝓒 ⟫ x y)
idtoiso 𝓒 x y p = J (λ y' q → CatIso ⟪ 𝓒 ⟫ x y') (CanCatIso 𝓒 x) p

isUniv : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') → Type (ℓ-max ℓ ℓ')
isUniv 𝓒 = ∀ x y → isEquiv (idtoiso 𝓒 x y)
\end{code}

needed for reasoning with isomorphisms:

\begin{code}
→[⟦_⟧⟨_⟩⟨_⟩_] : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') (x y : 𝒪𝒷 ⟪ 𝓒 ⟫)
               → CatIso ⟪ 𝓒 ⟫ x y → 𝒽 ⟪ 𝓒 ⟫ x y
→[⟦ 𝓒 ⟧⟨ x ⟩⟨ y ⟩ r , l , _ ] = r

←[⟦_⟧⟨_⟩⟨_⟩_] : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') (x y : 𝒪𝒷 ⟪ 𝓒 ⟫)
               → CatIso ⟪ 𝓒 ⟫ x y → 𝒽 ⟪ 𝓒 ⟫ y x
←[⟦ 𝓒 ⟧⟨ x ⟩⟨ y ⟩ r , l , _ ] = l 

transIsoNeutral : {ℓ ℓ' : Level} (𝓒 : PreCategory ℓ ℓ') (w x y z : 𝒪𝒷 ⟪ 𝓒 ⟫)
                  (p : w ≡ x) (q : y ≡ z) (f : 𝒽 ⟪ 𝓒 ⟫ w y)
               → transp (λ r → 𝒽 ⟪ 𝓒 ⟫ (p r) (q r)) i0 f ≡
                  𝑆⟦ 𝓒 ⟧ ←[⟦ 𝓒 ⟧⟨ w ⟩⟨ x ⟩ (idtoiso 𝓒 w x p) ]
                   (𝑆⟦ 𝓒 ⟧ f →[⟦ 𝓒 ⟧⟨ y ⟩⟨ z ⟩ (idtoiso 𝓒 y z q) ])
transIsoNeutral 𝓒 w x y z p q f =
 J (λ y' q' → transp (λ r → 𝒽 ⟪ 𝓒 ⟫ (p r) (q' r)) i0 f ≡
               𝑆⟦ 𝓒 ⟧ ←[⟦ 𝓒 ⟧⟨ w ⟩⟨ x ⟩ (idtoiso 𝓒 w x p) ]
               (𝑆⟦ 𝓒 ⟧ f →[⟦ 𝓒 ⟧⟨ y ⟩⟨ y' ⟩ (idtoiso 𝓒 y y' q') ]))
   (J (λ x' p' → transp (λ r → 𝒽 ⟪ 𝓒 ⟫ (p' r) _) i0 f ≡
                  𝑆⟦ 𝓒 ⟧ ←[⟦ 𝓒 ⟧⟨ w ⟩⟨ x' ⟩ (idtoiso 𝓒 w x' p') ]
                  (𝑆⟦ 𝓒 ⟧ f →[⟦ 𝓒 ⟧⟨ y ⟩⟨ y ⟩ (idtoiso 𝓒 y y _) ]))
      (transp (λ r → 𝒽 ⟪ 𝓒 ⟫ w y) i0 f ≡⟨ transportRefl f ⟩
      f ≡⟨ (sym (𝑆-ρ⟦ 𝓒 ⟧ f)) ∙ cong (𝑆⟦ 𝓒 ⟧ f) (sym (transportRefl (fst (CanCatIso 𝓒 y)))) ⟩
      𝑆⟦ 𝓒 ⟧ f →[⟦ 𝓒 ⟧⟨ y ⟩⟨ y ⟩ (idtoiso 𝓒 y y _) ]
        ≡⟨ (sym (𝑆-λ⟦ 𝓒 ⟧ _)) ∙
           cong (λ - → 𝑆⟦ 𝓒 ⟧ - (𝑆⟦ 𝓒 ⟧ f →[⟦ 𝓒 ⟧⟨ y ⟩⟨ y ⟩ (idtoiso 𝓒 y y refl) ]))
           (sym (transportRefl (fst (snd (CanCatIso 𝓒 w))))) ⟩
      𝑆⟦ 𝓒 ⟧ ←[⟦ 𝓒 ⟧⟨ w ⟩⟨ w ⟩ (idtoiso 𝓒 w w _) ]
      (𝑆⟦ 𝓒 ⟧ f →[⟦ 𝓒 ⟧⟨ y ⟩⟨ y ⟩ (idtoiso 𝓒 y y _) ]) ∎) p) q

