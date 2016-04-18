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
   infixl 8 _/̂_
   _/̂_ : ∀ {Γ} {P₀ P₀′ : Proc Γ} → ↓ P₀ → P₀ ⋉̂ P₀′ → ↓ P₀′
   ◻ /̂ _ = ◻
   [ ν ◻ ] /̂ νν-swapₗ _ = [ ν ◻ ]
   [ ν [ ν P′ ] ] /̂ νν-swapₗ P = [ ν [ ν subst ↓_ (swap-involutive P) ((swap *̃) P′) ] ]
   [ ν ◻ ] /̂ νν-swapᵣ _ = [ ν ◻ ]
   [ ν [ ν P′ ] ] /̂ νν-swapᵣ P = [ ν [ ν (swap *̃) P′ ] ]
   [ P ➕ Q ] /̂ (φ ➕₁ refl) = [ P /̂ φ ➕ Q ]
   [ P ➕ Q ] /̂ (refl ➕₂ ψ) = [ P ➕ Q /̂ ψ ]
   [ P │ Q ] /̂ (φ │₁ refl) = [ (P /̂ φ) │ Q ]
   [ P │ Q ] /̂ (refl │₂ ψ) = [ P │ (Q /̂ ψ) ]
   [ ν P ] /̂ ν φ = [ ν (P /̂ φ) ]
   [ ! P ] /̂ ! φ = [ ! (P /̂ φ) ]

   -- Image of a process slice in a (generalised) bound braid.
   infixl 8 _/_
   _/_ : ∀ {Γ} {P₀ P₀′ : Proc Γ} → ↓ P₀ → P₀ ⋉ P₀′ → ↓ P₀′
   ◻ / _ = ◻
   [ ν ◻ ] / νν-swapₗ _ = [ ν ◻ ]
   [ ν [ ν P′ ] ] / νν-swapₗ P = [ ν [ ν subst ↓_ (swap-involutive P) ((swap *̃) P′) ] ]
   [ ν ◻ ] / νν-swapᵣ _ = [ ν ◻ ]
   [ ν [ ν P′ ] ] / νν-swapᵣ P = [ ν [ ν (swap *̃) P′ ] ]
   [ Ο ] / Ο = [ Ο ]
   [ x •∙ P ] / (_ •∙ refl) = [ x •∙ P ]
   [ • x 〈 y 〉∙ P ] / (• _ 〈 _ 〉∙ refl) = [ • x 〈 y 〉∙ P ]
   [ P ➕ Q ] / (φ ➕₁ refl) = [ P / φ ➕ Q ]
   [ P ➕ Q ] / (refl ➕₂ ψ) = [ P ➕ Q / ψ ]
   [ P │ Q ] / (φ │ ψ) = [ (P / φ) │ (Q / ψ) ]
   [ ν P ] / ν φ = [ ν (P / φ) ]
   [ ! P ] / ! φ = [ ! (P / φ) ]

   -- "Obviously" true, but not quite definitionally so.
   /-ν : ∀ {Γ} {P₀ P₀′ : Proc (Γ + 1)} (P : ↓ P₀) {φ : P₀ ⋉ P₀′} → [ ν P ] / ν φ ≡ [ ν (P / φ) ]
   /-ν ◻ = refl
   /-ν [ Ο ] = refl
   /-ν [ _ •∙ _ ] = refl
   /-ν [ • _ 〈 _ 〉∙ _ ] = refl
   /-ν [ _ ➕ _ ] = refl
   /-ν [ _ │ _ ] = refl
   /-ν [ ν _ ] = refl
   /-ν [ ! _ ] = refl
