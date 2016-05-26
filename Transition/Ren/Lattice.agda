-- Lift transition renamings to prefix lattices. Convenient to have separate lemmas for action and target.
module Transition.Ren.Lattice where

   open import ConcurrentSlicingCommon
   open import Action using (Actionᵇ; Actionᶜ; _ᵇ; _ᶜ)
   open import Action.Ren.Lattice renaming (_* to _ᴬ*̃)
   import Lattice; open Lattice.Prefixes ⦃...⦄ using (↓_)
   open import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren)
   open import Ren.Lattice using (_*; _ᴿ+_)
   open import Transition using (_—[_-_]→_)
   open import Transition.Lattice as ᵀ̃ using (target; action)
   open import Transition.Ren using (_*ᶜ; _*ᵇ)

   postulate
      renᶜ-target-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᶜ - _ ]→ R₀) →
                        (ρ′ : ↓ ρ) (P : ↓ P₀) → (ρ′ *̃) (target E P) ≡ target ((ρ *ᶜ) E) ((ρ′ *̃) P)
      renᶜ-action-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᶜ - _ ]→ R₀) →
                         (ρ′ : ↓ ρ) (P : ↓ P₀) → (ρ′ ᴬ*̃) (action E P) ≡ action ((ρ *ᶜ) E) ((ρ′ *̃) P)
      renᵇ-target-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᵇ - _ ]→ R₀) →
                         (ρ′ : ↓ ρ) (P : ↓ P₀) → ((ρ′ ᴿ+ 1) *̃) (target E P) ≡ target ((ρ *ᵇ) E) ((ρ′ *̃) P)
      renᵇ-action-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᵇ - _ ]→ R₀) →
                         (ρ′ : ↓ ρ) (P : ↓ P₀) → (ρ′ ᴬ*̃) (action E P) ≡ action ((ρ *ᵇ) E) ((ρ′ *̃) P)
