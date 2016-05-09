module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖-✓); open _ᴬ⌣_
   open import Braiding.Proc using (module _⋉̂_); open _⋉̂_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Name using (zero)
   open import Proc as ᴾ using (Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (↓_; ↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (suc); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (swap)
   open import Ren.Properties
   open import Transition using (_—[_-_]→_; target)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁; open Delta′
   open import Transition.Concur.Cofinal using (⋉̂[_,_,_]; ⊖₁-✓)

   braiding : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
              (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Q = S (⊖₁ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸))) in
              ⋉̂[ Γ , 𝑎 , zero ] Q Q′ → ↓ Q → ↓ Q′
   braiding (E ᵇ│ᵇ F) γ P = subst ↓_ (sym (cong₂ _│_ (swap∘push (target E)) (swap∘suc-push (target F)))) ((swap *̃) P)
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
   braiding (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) γ P′ = subst ↓_ (cong₂ _│_ (swap∘push∘push P) (⊖₁-✓ 𝐹)) ((swap *̃) P′)
   braiding (P │ᵇᶜ 𝐹) γ rewrite γ = idᶠ
   braiding (P │ᶜᵇ 𝐹) γ rewrite γ = idᶠ
   braiding (P │ᶜᶜ 𝐹) γ rewrite γ = idᶠ
   braiding (P │ᵛᵛ 𝐹) = braid̂
   braiding {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) γ rewrite γ = idᶠ
   braiding {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) γ P = subst ↓_ (cong₂ _│_ (⊖₁-✓ 𝐸) (swap∘push∘push Q)) ((swap *̃) P)
   braiding (𝐸 ᵇᶜ│ Q) γ rewrite γ = idᶠ
   braiding (𝐸 ᶜᵇ│ Q) γ rewrite γ = idᶠ
   braiding (𝐸 ᶜᶜ│ Q) γ rewrite γ = idᶠ
   braiding (𝐸 ᵛᵛ│ Q) = braid̂
   braiding (𝐸 │• 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │•ᵥ 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥ• 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥ 𝐹) γ rewrite γ = idᶠ
   braiding (𝐸 │ᵥ′ 𝐹) = braid̂
   braiding (ν• 𝐸) γ rewrite γ = idᶠ
   braiding (ν•ᵇ 𝐸) γ P = subst ↓_ (cong (ᴿ.swap *) (⊖₁-✓ 𝐸)) ((swap *̃) P)
   braiding (ν•ᶜ 𝐸) γ rewrite γ = idᶠ
   braiding (νᵇᵇ_ {a = x •} {a} 𝐸) γ P = {!!}
   braiding (νᵇᵇ_ {a = • x} {u •} 𝐸) γ P =
      subst ↓_ (cong ν_ (trans (sym (swap∘suc-swap∘swap _)) (cong (ᴿ.swap *) (cong (suc ᴿ.swap *) (⊖₁-✓ 𝐸))))) ((swap *̃) P)
   braiding (νᵇᵇ_ {a = • x} {• u} 𝐸) γ P =
      subst ↓_ (cong ν_ (trans (sym (swap∘suc-swap∘swap _)) (cong (ᴿ.swap *) (cong (suc ᴿ.swap *) (⊖₁-✓ 𝐸))))) ((swap *̃) P)
   braiding (νˣˣ 𝐸) γ rewrite γ = idᶠ
   braiding (νᵇᶜ 𝐸) γ rewrite γ = idᶠ
   braiding (νᶜᵇ 𝐸) γ rewrite γ = idᶠ
   braiding (νᶜᶜ 𝐸) γ rewrite γ = idᶠ
   braiding (νᵛᵛ 𝐸) = braid̂
   braiding (! 𝐸) = braiding 𝐸
