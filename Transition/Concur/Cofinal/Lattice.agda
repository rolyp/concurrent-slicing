module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖-✓); open _ᴬ⌣_
   open import Braiding.Proc using (module _⋉̂_); open _⋉̂_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Name using (zero; suc)
   open import Proc as ᴾ using (Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (↓_; ↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition using (_—[_-_]→_; target)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁; open Delta′
   open import Transition.Concur.Cofinal using (⋉̂[_,_,_])

   braiding : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
           (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Q = S (⊖₁ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸))) in
           ⋉̂[ Γ , 𝑎 , zero ] Q Q′ → ↓ Q → ↓ Q′
   braiding (E ᵇ│ᵇ F) γ P = {!!}
   braiding (E ᵇ│ᶜ F) refl = idᶠ
   braiding (E ᶜ│ᵇ F) refl = idᶠ
   braiding (E ᶜ│ᶜ F) refl = idᶠ
   braiding (𝐸 │•ᵇ F) γ rewrite γ = idᶠ
   braiding (𝐸 │•ᶜ F) γ rewrite γ = idᶠ
   braiding (E ᵇ│• 𝐹) γ rewrite γ = idᶠ
   braiding (E ᶜ│• 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥᵇ F) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥᶜ F) γ rewrite γ = idᶠ
   braiding (E ᵇ│ᵥ 𝐹) γ rewrite γ = idᶠ
   braiding (E ᶜ│ᵥ 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 ➕₁ Q) = braiding 𝐸
   braiding (_│ᵇᵇ_ {𝑎 = ˣ∇ˣ} P 𝐹) γ rewrite γ = idᶠ
   braiding (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) γ P₁ = {!!}
   braiding (P │ᵇᶜ 𝐹) γ rewrite γ = idᶠ
   braiding (P │ᶜᵇ 𝐹) γ rewrite γ = idᶠ
   braiding (P │ᶜᶜ 𝐹) γ rewrite γ = idᶠ
   braiding (P │ᵛᵛ 𝐹) γ P₁ = {!!}
   braiding {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) γ rewrite γ = idᶠ
   braiding {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) γ P₁ = {!!}
   braiding (𝐸 ᵇᶜ│ Q) γ rewrite γ = idᶠ
   braiding (𝐸 ᶜᵇ│ Q) γ rewrite γ = idᶠ
   braiding (𝐸 ᶜᶜ│ Q) γ rewrite γ = idᶠ
   braiding (𝐸 ᵛᵛ│ Q) γ P = braid̂ γ P
   braiding (𝐸 │• 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │•ᵥ 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥ• 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥ 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥ′ 𝐹) γ P₁ = {!!}
   braiding (ν• 𝐸) γ rewrite γ = idᶠ
   braiding (ν•ᵇ 𝐸) γ P₁ = {!!}
   braiding (ν•ᶜ 𝐸) γ rewrite γ = idᶠ
   braiding (νᵇᵇ_ {a = x •} {a} 𝐸) γ P₁ = {!!}
   braiding (νᵇᵇ_ {a = • x} {u •} 𝐸) γ P₁ = {!!}
   braiding (νᵇᵇ_ {a = • x} {• u} 𝐸) γ P₁ = {!!}
   braiding (νˣˣ 𝐸) γ rewrite γ = idᶠ
   braiding (νᵇᶜ 𝐸) γ rewrite γ = idᶠ
   braiding (νᶜᵇ 𝐸) γ rewrite γ = idᶠ
   braiding (νᶜᶜ 𝐸) γ rewrite γ = idᶠ
   braiding (νᵛᵛ 𝐸) γ P₁ = {!!}
   braiding (! 𝐸) = braiding 𝐸
