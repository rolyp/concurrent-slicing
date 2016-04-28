module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖-✓); open _ᴬ⌣_
   open import Braiding.Proc using (module _⋉̂_); open _⋉̂_
   open import Name using (zero; suc)
   open import Proc as ᴾ using (Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (↓_; ↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition using (_—[_-_]→_; target)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁; open Delta′
   open import Transition.Concur.Cofinal using (⋉̂[_,_,_])

   braid : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
           (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Q = S (⊖₁ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸))) in
           ⋉̂[ Γ , 𝑎 , zero ] Q Q′ → ↓ Q → ↓ Q′
   braid (E ᵇ│ᵇ F) γ P = {!!}
   braid (E ᵇ│ᶜ F) refl = idᶠ
   braid (E ᶜ│ᵇ F) refl = idᶠ
   braid (E ᶜ│ᶜ F) refl = idᶠ
   braid (𝐸 │•ᵇ F) γ rewrite γ = idᶠ
   braid (𝐸 │•ᶜ F) γ rewrite γ = idᶠ
   braid (E ᵇ│• 𝐹) γ rewrite γ = idᶠ
   braid (E ᶜ│• 𝐹) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥᵇ F) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥᶜ F) γ rewrite γ = idᶠ
   braid (E ᵇ│ᵥ 𝐹) γ rewrite γ = idᶠ
   braid (E ᶜ│ᵥ 𝐹) γ rewrite γ = idᶠ
   braid (𝐸 ➕₁ Q) = braid 𝐸
   braid (_│ᵇᵇ_ {𝑎 = ˣ∇ˣ} P 𝐹) γ rewrite γ = idᶠ
   braid (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) γ P₁ = {!!}
   braid (P │ᵇᶜ 𝐹) γ rewrite γ = idᶠ
   braid (P │ᶜᵇ 𝐹) γ rewrite γ = idᶠ
   braid (P │ᶜᶜ 𝐹) γ rewrite γ = idᶠ
   braid (P │ᵛᵛ 𝐹) γ P₁ = {!!}
   braid {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) γ rewrite γ = idᶠ
   braid {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) γ P₁ = {!!}
   braid (𝐸 ᵇᶜ│ Q) γ rewrite γ = idᶠ
   braid (𝐸 ᶜᵇ│ Q) γ rewrite γ = idᶠ
   braid (𝐸 ᶜᶜ│ Q) γ rewrite γ = idᶠ
   braid (𝐸 ᵛᵛ│ Q) γ ◻ = ◻
   braid (𝐸 ᵛᵛ│ Q) (γ │₁ refl) [ R │ S′ ] = [ braid 𝐸 γ R │ S′ ]
   braid (𝐸 ᵛᵛ│ Q) (x │₂ γ) [ R │ S′ ] = {!!}
   braid (𝐸 │• 𝐹) γ rewrite γ = idᶠ
   braid (𝐸 │•ᵥ 𝐹) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥ• 𝐹) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥ 𝐹) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥ′ 𝐹) γ P₁ = {!!}
   braid (ν• 𝐸) γ rewrite γ = idᶠ
   braid (ν•ᵇ 𝐸) γ P₁ = {!!}
   braid (ν•ᶜ 𝐸) γ rewrite γ = idᶠ
   braid (νᵇᵇ_ {a = x •} {a} 𝐸) γ P₁ = {!!}
   braid (νᵇᵇ_ {a = • x} {u •} 𝐸) γ P₁ = {!!}
   braid (νᵇᵇ_ {a = • x} {• u} 𝐸) γ P₁ = {!!}
   braid (νˣˣ 𝐸) γ rewrite γ = idᶠ
   braid (νᵇᶜ 𝐸) γ rewrite γ = idᶠ
   braid (νᶜᵇ 𝐸) γ rewrite γ = idᶠ
   braid (νᶜᶜ 𝐸) γ rewrite γ = idᶠ
   braid (νᵛᵛ 𝐸) γ P₁ = {!!}
   braid (! 𝐸) = braid 𝐸
