module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖-✓); open _ᴬ⌣_
   open import Name using (zero)
   open import Proc using (Proc↱)
   open import Proc.Lattice as ᴾ̃ using (↓_; ↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁; open Delta′
   open import Transition.Concur.Cofinal using (⋉̂[_,_,_])

braid : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
        (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Q = S (⊖₁ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸))) in
        ⋉̂[ Γ , 𝑎 , zero ] Q Q′ → ↓ Q → ↓ Q′
braid (E ᵇ│ᵇ F) γ ◻ = {!!}
braid (E ᵇ│ᵇ F) γ [ _ │ _ ] = {!!}
braid (E ᵇ│ᶜ F) refl = idᶠ
braid (E ᶜ│ᵇ F) refl = idᶠ
braid (E ᶜ│ᶜ F) refl = idᶠ
braid (𝐸 │•ᵇ F) γ P₁ = {!!}
braid (𝐸 │•ᶜ F) γ P₁ = {!!}
braid (E ᵇ│• 𝐸) γ P₁ = {!!}
braid (E ᶜ│• 𝐸) γ P₁ = {!!}
braid (𝐸 │ᵥᵇ F) γ P₁ = {!!}
braid (𝐸 │ᵥᶜ F) γ P₁ = {!!}
braid (E ᵇ│ᵥ 𝐸) γ P₁ = {!!}
braid (E ᶜ│ᵥ 𝐸) γ P₁ = {!!}
braid (𝐸 ➕₁ Q) γ P₁ = {!!}
braid (P │ᵇᵇ 𝐸) γ P₁ = {!!}
braid (P │ᵇᶜ 𝐸) γ P₁ = {!!}
braid (P │ᶜᵇ 𝐸) γ P₁ = {!!}
braid (P │ᶜᶜ 𝐸) γ P₁ = {!!}
braid (P │ᵛᵛ 𝐸) γ P₁ = {!!}
braid (𝐸 ᵇᵇ│ Q) γ P₁ = {!!}
braid (𝐸 ᵇᶜ│ Q) γ P₁ = {!!}
braid (𝐸 ᶜᵇ│ Q) γ P₁ = {!!}
braid (𝐸 ᶜᶜ│ Q) γ P₁ = {!!}
braid (𝐸 ᵛᵛ│ Q) γ P₁ = {!!}
braid (𝐸 │• 𝐸₁) γ P₁ = {!!}
braid (𝐸 │•ᵥ 𝐸₁) γ P₁ = {!!}
braid (𝐸 │ᵥ• 𝐸₁) γ P₁ = {!!}
braid (𝐸 │ᵥ 𝐸₁) γ P₁ = {!!}
braid (𝐸 │ᵥ′ 𝐸₁) γ P₁ = {!!}
braid (ν• 𝐸) γ P₁ = {!!}
braid (ν•ᵇ 𝐸) γ P₁ = {!!}
braid (ν•ᶜ 𝐸) γ P₁ = {!!}
braid (νᵇᵇ 𝐸) γ P₁ = {!!}
braid (νˣˣ 𝐸) γ P₁ = {!!}
braid (νᵇᶜ 𝐸) γ P₁ = {!!}
braid (νᶜᵇ 𝐸) γ P₁ = {!!}
braid (νᶜᶜ 𝐸) γ P₁ = {!!}
braid (νᵛᵛ 𝐸) γ P₁ = {!!}
braid (! 𝐸) γ P₁ = {!!}
