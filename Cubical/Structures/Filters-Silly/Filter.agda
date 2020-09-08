{- 
  Defining filters as a sort of subset of a poset.

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Filters-Silly.Filter where

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Prod

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic renaming (¬_ to ~_ ; ⊥ to abs)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Cubical.Structures.Poset

module _ {ℓ ℓ' : Level} where

 subPoset : (P : Poset ℓ ℓ') → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
 subPoset P = Σ (Poset ℓ ℓ') (λ F → 
              Σ (fst F → fst P) (λ f → 
               (isEmbedding f) ×
               (isOrderPreserving ((fst F) , (rel F)) ((fst P) , rel P) f)))

 
 isSubPoset : Type ℓ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
 isSubPoset F = Σ (PosetStructure ℓ' F) (λ pS →
                Σ (Poset ℓ ℓ') (λ P →
                Σ (F → fst P) (λ f →
                 (isEmbedding f) ×
                 (isOrderPreserving (F , rel (F , pS)) (fst P , rel P) f))))

 Nonempty : (F : Type ℓ) → isSubPoset F → Type ℓ
 Nonempty F sF = ¬ (F → ⊥)

 isPropNonempty : (F : Type ℓ) → (sF : isSubPoset F) → isProp (Nonempty F sF)
 isPropNonempty F sF = isProp¬ (F → ⊥)
 
 DownwardDirected : (F : Type ℓ) → (isSubPoset F) → Type (ℓ-max ℓ ℓ')
 DownwardDirected F ((_⊑₀_ , _) , (P , _⊑₁_ , _) , f , (_ , _)) =
  ∀ x y → Σ F (λ z → [ z ⊑₀ x ] × [ z ⊑₀ y ])

 UpwardClosed : (F : Type ℓ) → (isSubPoset F) → Type (ℓ-max ℓ ℓ')
 UpwardClosed F ((_⊑₀_ , _) , (P , _⊑₁_ , _) , f , (_ , _)) =
  ∀ x y → (Σ F (λ u → f u ≡ x)) → [ x ⊑₁ y ] → (Σ F (λ u → f u ≡ y))

 satFilterStr : Type ℓ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
 satFilterStr F =
  Σ (isSubPoset F)
    (λ sF → Nonempty F sF × DownwardDirected F sF × UpwardClosed F sF)

 Filter : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
 Filter = TypeWithStr ℓ satFilterStr
