module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖-✓); open _ᴬ⌣_
   open import Braiding.Proc using (module _⋉̂_); open _⋉̂_
   open import Name using (zero; suc)
   open import Proc as ᴾ using (Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (↓_; ↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_)
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
   braid (E ᵇ│• 𝐸) γ rewrite γ = idᶠ
   braid (E ᶜ│• 𝐸) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥᵇ F) γ rewrite γ = idᶠ
   braid (𝐸 │ᵥᶜ F) γ rewrite γ = idᶠ
   braid (E ᵇ│ᵥ 𝐸) γ rewrite γ = idᶠ
   braid (E ᶜ│ᵥ 𝐸) γ rewrite γ = idᶠ
   braid (𝐸 ➕₁ Q) γ = braid 𝐸 γ
   braid (P │ᵇᵇ 𝐸) γ P₁ = {!!}
   braid (P │ᵇᶜ 𝐸) γ rewrite γ = idᶠ
   braid (P │ᶜᵇ 𝐸) γ rewrite γ = idᶠ
   braid (P │ᶜᶜ 𝐸) γ rewrite γ = idᶠ
   braid (P │ᵛᵛ 𝐸) γ P₁ = {!!}
   braid (𝐸 ᵇᵇ│ Q) γ P₁ = {!!}
   braid (𝐸 ᵇᶜ│ Q₀) γ rewrite γ = idᶠ
   braid (𝐸 ᶜᵇ│ Q) γ rewrite γ = idᶠ
   braid (𝐸 ᶜᶜ│ Q) γ rewrite γ = idᶠ
   braid (𝐸 ᵛᵛ│ Q) γ ◻ = {!!}
   braid (𝐸 ᵛᵛ│ Q) (γ │₁ refl) [ R │ S′ ] = [ braid 𝐸 γ R │ S′ ]
   braid (𝐸 ᵛᵛ│ Q) (x │₂ γ) [ R │ S′ ] = {!!}
   braid (𝐸 │• 𝐸₁) γ rewrite γ = idᶠ
   braid (𝐸 │•ᵥ 𝐸₁) γ rewrite γ = idᶠ
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
