module Action.Concur.Lattice where

   open import ConcurrentSlicingCommon

   open import Action using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖); open _ᴬ⌣_
   open import Action.Lattice as ᴬ̃ using (); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_
   open import Action.Ren.Lattice using (_*)
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using ()
   open import Name.Lattice as ᴺ̃ using (suc; zero)
   open import Ren.Lattice using (push)

   -- Need more consistent naming here. Lattice counterpart of ᴬ/, although this produces a/a'.
   residual : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → ↓ a → ↓ π₂ (ᴬ⊖ a⌣a′)
   residual ˣ∇ˣ ◻ = ◻
   residual ˣ∇ˣ [ • x ﹙ y ﹚ ᵇ ] = [ • ᴺ.suc x 〈 y 〉 ᶜ ]
   residual ᵇ∇ᵇ = push *
   residual ᵇ∇ᶜ = idᶠ
   residual ᶜ∇ᵇ = push *
   residual ᶜ∇ᶜ = idᶠ
   residual ᵛ∇ᵛ = idᶠ

   inj-residual : ∀ {Γ} {a₀ a′₀ : Action Γ} (a⌣a′ : a₀ ᴬ⌣ a′₀) (a a′ : ↓ a₀) → residual a⌣a′ a ≡ residual a⌣a′ a′ → a ≡ a′
   inj-residual ˣ∇ˣ ◻ ◻ _ = refl
   inj-residual ˣ∇ˣ ◻ [ • x ﹙ y ﹚ ᵇ ] ()
   inj-residual ˣ∇ˣ [ • x ﹙ y ﹚ ᵇ ] ◻ ()
   inj-residual ˣ∇ˣ [ • x ﹙ y ﹚ ᵇ ] [ • .x ﹙ y′ ﹚ ᵇ ] q = {!!}
   inj-residual ᵇ∇ᵇ a a′ q = {!!}
   inj-residual ᵇ∇ᶜ a .a refl = {!!}
   inj-residual ᶜ∇ᵇ a a′ q = {!!}
   inj-residual ᶜ∇ᶜ a .a refl = refl
   inj-residual ᵛ∇ᵛ a .a refl = refl
