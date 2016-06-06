module Action.Ren.Lattice where

   open import Action using (Action; Actionᵇ; Actionᶜ)
   open import Action.Lattice as ᴬ̃ using (↓ᵇ_; ↓ᶜ_); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_
   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Name.Lattice
   import Action.Ren
   open import Ren as ᴿ using (Ren);
      open ᴿ.Renameable ⦃...⦄ renaming (_* to _*′)
   import Ren.Lattice as ᴿ̃

   infixr 8 _*ᵇ _*
   _*ᵇ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {a : Actionᵇ Γ} → ↓ ρ → ↓ᵇ a → ↓ᵇ (ρ *′) a
   _*ᶜ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {a : Actionᶜ Γ} → ↓ ρ → ↓ᶜ a → ↓ᶜ (ρ *′) a
   _* : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {a : Action Γ} → ↓ ρ → ↓ a → ↓ (ρ *′) a

   (_*ᵇ {ρ = ρ₀} _) (x •) = ρ₀ x •
   (_*ᵇ {ρ = ρ₀} _) (• x) = • ρ₀ x

   (_*ᶜ {ρ = ρ₀} ρ) • x 〈 y 〉 = • ρ₀ x 〈 (ρ ᴿ̃.*) y 〉
   (ρ *ᶜ) τ = τ

   (ρ *) ◻ = ◻
   (ρ *) [ a ᵇ ] = [ (ρ *ᵇ) a ᵇ ]
   (ρ *) [ a ᶜ ] = [ (ρ *ᶜ) a ᶜ ]
