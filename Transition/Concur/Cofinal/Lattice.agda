module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_); open _ᴬ⌣_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Name using (Cxt)
   open import Proc.Lattice as ᴾ̃ using (↓_); open ᴾ̃.↓_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (_ᴿ+_; swap)
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁)
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁)
   open import Transition.Lattice.GaloisConnection using (fwd)

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} → ⋈̂[ Γ , 𝑎 , Δ ] P P′ → ↓ P → ↓ P′
   braiding ˣ∇ˣ refl = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   open Delta′

   -- Not sure of the naming convention to use here.
   wibble : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) →
            let f = fwd (E/E′ (⊖₁ 𝐸)) ∘ᶠ π₂ ∘ᶠ fwd E′ in
            let g = braiding 𝑎 (γ₁ 𝐸) ∘ᶠ π₂ ∘ᶠ fwd (E′/E (⊖₁ 𝐸)) ∘ᶠ π₂ ∘ᶠ fwd E in ⊤
   wibble = {!!}
