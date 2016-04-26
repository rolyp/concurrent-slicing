module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖-✓)
   open import Name using (zero)
   open import Proc using (Proc↱)
   open import Proc.Lattice using (↓_)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ⊖₁); open Delta′
   open import Transition.Concur.Cofinal using (⋉̂[_,_,_])

braid : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
        (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Q = S (⊖₁ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸))) in
        ⋉̂[ Γ , 𝑎 , zero ] Q Q′ → ↓ Q → ↓ Q′
braid E = {!!}
