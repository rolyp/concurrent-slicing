module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; inc)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬγ); open _ᴬ⌣_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Name using (Cxt; _+_)
   open import Proc using (Proc; Proc↱)
   open import Proc.Lattice as ᴾ̃ using (↓_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (_ᴿ+_; swap)
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁
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

   -- Can't see a way to inline this into the proposition being proven.
   coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
               let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
   coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

   -- Not sure of the naming convention to use here.
   wibble : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) →
            coerceCxt 𝑎 ∘ᶠ π₂ ∘ᶠ fwd (E/E′ (⊖₁ 𝐸)) ∘ᶠ π₂ ∘ᶠ fwd E′ ≃ₑ
            braiding 𝑎 (γ₁ 𝐸) ∘ᶠ π₂ ∘ᶠ fwd (E′/E (⊖₁ 𝐸)) ∘ᶠ π₂ ∘ᶠ fwd E
   wibble _ ◻ = {!!}
   wibble (𝐸 ➕₁ Q) [ P ➕ _ ] = wibble 𝐸 P
   wibble {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐸) P₁ = {!!}
   wibble {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) P₁ = {!!}
   wibble {𝑎 = ˣ∇ˣ} (ν• 𝐸) P₁ = {!!}
   wibble {𝑎 = ˣ∇ˣ} (νˣˣ 𝐸) P₁ = {!!}
   wibble {𝑎 = ˣ∇ˣ} (! 𝐸) P₁ = {!!}
   wibble {𝑎 = ᵇ∇ᵇ} 𝐸 P₁ = {!!}
   wibble {𝑎 = ᵇ∇ᶜ} 𝐸 P₁ = {!!}
   wibble {𝑎 = ᶜ∇ᵇ} 𝐸 P₁ = {!!}
   wibble {𝑎 = ᶜ∇ᶜ} 𝐸 P₁ = {!!}
   wibble {𝑎 = ᵛ∇ᵛ} 𝐸 P₁ = {!!}
