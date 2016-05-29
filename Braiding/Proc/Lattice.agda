module Braiding.Proc.Lattice where

   open import ConcurrentSlicingCommon hiding (trans)
   import Relation.Binary.EqReasoning as EqReasoning

   import Lattice; open Lattice.Prefixes ⦃...⦄ using (↓_)
   open import Name using (_+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   import Ren as ᴿ; open ᴿ.Renameable ⦃...⦄ using (_*)
   open import Ren.Lattice using (swap)
   open import Ren.Properties
   open import Braiding.Proc using (_⋉̂_; module _⋉̂_; ⋉̂-sym; _⋉_; module _⋉_); open _⋉̂_; open _⋉_

   -- Image of a process slice in a bound braid.
   braid̂ : ∀ {Γ} {P₀ P₀′ : Proc Γ} → P₀ ⋉̂ P₀′ → ↓ P₀ → ↓ P₀′
   braid̂ _ ◻ = ◻
   braid̂ (νν-swapₗ _) [ ν ◻ ]  = [ ν ◻ ]
   braid̂ (νν-swapₗ P) [ ν [ ν P′ ] ] = [ ν [ ν subst ↓_ (swap-involutive P) ((swap *̃) P′) ] ]
   braid̂ (νν-swapᵣ _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ (νν-swapᵣ P) [ ν [ ν P′ ] ] = [ ν [ ν (swap *̃) P′ ] ]
   braid̂ (φ ➕₁ refl) [ P ➕ Q ] = [ braid̂ φ P ➕ Q ]
   braid̂ (refl ➕₂ ψ) [ P ➕ Q ] = [ P ➕ braid̂ ψ Q ]
   braid̂ (φ │₁ refl) [ P │ Q ] = [ (braid̂ φ P) │ Q ]
   braid̂ (refl │₂ ψ) [ P │ Q ] = [ P │ (braid̂ ψ Q) ]
   braid̂ (ν φ) [ ν P ] = [ ν (braid̂ φ P) ]
   braid̂ (! φ) [ ! P ] = [ ! (braid̂ φ P) ]

   -- Image of a process slice in a (generalised) bound braid.
   braid : ∀ {Γ} {P₀ P₀′ : Proc Γ} → P₀ ⋉ P₀′ → ↓ P₀ → ↓ P₀′
   braid _ ◻ = ◻
   braid (νν-swapₗ _) [ ν ◻ ] = [ ν ◻ ]
   braid (νν-swapₗ P) [ ν [ ν P′ ] ] = [ ν [ ν subst ↓_ (swap-involutive P) ((swap *̃) P′) ] ]
   braid (νν-swapᵣ _) [ ν ◻ ] = [ ν ◻ ]
   braid (νν-swapᵣ P) [ ν [ ν P′ ] ] = [ ν [ ν (swap *̃) P′ ] ]
   braid Ο [ Ο ] = [ Ο ]
   braid (x •∙ refl) [ ._ •∙ P ] = [ x •∙ P ]
   braid (• x 〈 _ 〉∙ refl) [ • .x 〈 y 〉∙ P ] = [ • x 〈 y 〉∙ P ]
   braid (φ ➕₁ refl) [ P ➕ Q ] = [ braid φ P ➕ Q ]
   braid (refl ➕₂ ψ) [ P ➕ Q ] = [ P ➕ braid ψ Q ]
   braid (φ │ ψ) [ P │ Q ] = [ (braid φ P) │ (braid ψ Q) ]
   braid (ν φ) [ ν P ] = [ ν (braid φ P) ]
   braid (! φ) [ ! P ] = [ ! (braid φ P) ]

   -- "Obviously" true, but not quite definitionally so.
   braid-ν : ∀ {Γ} {P₀ P₀′ : Proc (Γ + 1)} (P : ↓ P₀) {φ : P₀ ⋉ P₀′} → braid (ν φ) [ ν P ] ≡ [ ν (braid φ P) ]
   braid-ν ◻ = refl
   braid-ν [ Ο ] = refl
   braid-ν [ _ •∙ _ ] = refl
   braid-ν [ • _ 〈 _ 〉∙ _ ] = refl
   braid-ν [ _ ➕ _ ] = refl
   braid-ν [ _ │ _ ] = refl
   braid-ν [ ν _ ] = refl
   braid-ν [ ! _ ] = refl
