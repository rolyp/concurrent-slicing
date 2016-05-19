module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬγ); open _ᴬ⌣_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name using (Cxt; _+_)
   open import Proc as ᴾ using (Proc; Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (_ᴿ+_; swap; push)
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁)
   open import Transition.Lattice using (fwd; step)
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} → ⋈̂[ Γ , 𝑎 , Δ ] P P′ → ↓ P → ↓ P′
   braiding ˣ∇ˣ refl = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   ren-fwd-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {Q₀ a S₀} (F : Q₀ —[ a ᶜ - _ ]→ S₀) →
          (ρ′ : ↓ ρ) (Q : ↓ Q₀) → (ρ′ *̃) (π₂ (fwd F Q)) ≡ π₂ (fwd ((ρ *ᶜ) F) ((ρ′ *̃) Q))
   ren-fwd-comm = {!!}

   open Delta′

   -- Can't see a way to inline this into the proposition being proven.
   coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
               let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
   coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

   -- Not sure of the naming convention to use here.
   wibble : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
            coerceCxt 𝑎 (π₂ (fwd (E/E′ (⊖₁ 𝐸)) (π₂ (fwd E′ P′)))) ≡
            braiding 𝑎 (γ₁ 𝐸) (π₂ (fwd (E′/E (⊖₁ 𝐸)) (π₂ (fwd E P′))))
   wibble _ ◻ = {!!}
   wibble {E = .E ᵇ│ ._} {E′ = ._ │ᵇ .F} (E ᵇ│ᵇ F) [ P │ Q ] = {!!}
   wibble (E ᵇ│ᶜ F) [ P │ Q ] = cong (λ Q′ → [ _ │ Q′ ]) (ren-fwd-comm F push Q)
   wibble (E ᶜ│ᵇ F) [ P │ Q ] = cong (λ P′ → [ P′ │ _ ]) (sym (ren-fwd-comm E push P))
   wibble 𝐸 P = {!!}
{-
   wibble (E ᶜ│ᶜ F) P₁ = {!!}
   wibble (𝐸 │•ᵇ F) P₁ = {!!}
   wibble (𝐸 │•ᶜ F) P₁ = {!!}
   wibble (E ᵇ│• 𝐸) P₁ = {!!}
   wibble (E ᶜ│• 𝐸) P₁ = {!!}
   wibble (𝐸 │ᵥᵇ F) P₁ = {!!}
   wibble (𝐸 │ᵥᶜ F) P₁ = {!!}
   wibble (E ᵇ│ᵥ 𝐸) P₁ = {!!}
   wibble (E ᶜ│ᵥ 𝐸) P₁ = {!!}
   wibble (𝐸 ➕₁ Q) P₁ = {!!}
   wibble (P │ᵇᵇ 𝐸) P₁ = {!!}
   wibble (P │ᵇᶜ 𝐸) P₁ = {!!}
   wibble (P │ᶜᵇ 𝐸) P₁ = {!!}
   wibble (P │ᶜᶜ 𝐸) P₁ = {!!}
   wibble (P │ᵛᵛ 𝐸) P₁ = {!!}
   wibble (𝐸 ᵇᵇ│ Q) P₁ = {!!}
   wibble (𝐸 ᵇᶜ│ Q) P₁ = {!!}
   wibble (𝐸 ᶜᵇ│ Q) P₁ = {!!}
   wibble (𝐸 ᶜᶜ│ Q) P₁ = {!!}
   wibble (𝐸 ᵛᵛ│ Q) P₁ = {!!}
   wibble (𝐸 │• 𝐸₁) P₁ = {!!}
   wibble (𝐸 │•ᵥ 𝐸₁) P₁ = {!!}
   wibble (𝐸 │ᵥ• 𝐸₁) P₁ = {!!}
   wibble (𝐸 │ᵥ 𝐸₁) P₁ = {!!}
   wibble (𝐸 │ᵥ′ 𝐸₁) P₁ = {!!}
   wibble (ν• 𝐸) P₁ = {!!}
   wibble (ν•ᵇ 𝐸) P₁ = {!!}
   wibble (ν•ᶜ 𝐸) P₁ = {!!}
   wibble (νᵇᵇ 𝐸) P₁ = {!!}
   wibble (νˣˣ 𝐸) P₁ = {!!}
   wibble (νᵇᶜ 𝐸) P₁ = {!!}
   wibble (νᶜᵇ 𝐸) P₁ = {!!}
   wibble (νᶜᶜ 𝐸) P₁ = {!!}
   wibble (νᵛᵛ 𝐸) P₁ = {!!}
   wibble (! 𝐸) P₁ = {!!}
-}
