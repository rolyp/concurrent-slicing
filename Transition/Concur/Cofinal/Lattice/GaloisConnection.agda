module Transition.Concur.Cofinal.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖-✓)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (zero)
   open import Proc as ᴾ using (Proc↱)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ⊖₁); open Delta′
   open import Transition.Concur.Cofinal using (⋉̂[_,_,_])
   open import Transition.Concur.Cofinal.Lattice using (braiding)

   gc : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
        (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Q = S (⊖₁ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸))) in
        (γ : ⋉̂[ Γ , 𝑎 , zero ] Q Q′) → GaloisConnection (poset {a = Q}) (poset {a = Q′})
   gc γ = ⟪ braiding γ , braiding (⋉̂-sym γ) ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braiding γ ∘ᶠ ≤ᴸ⇒≤;
               g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braiding (⋉̂-sym γ) ∘ᶠ ≤ᴸ⇒≤;
               g∘f≤id = λ P → ≤⇒≤ᴸ (≤-reflexive («iso P γ));
               id≤f∘g = λ P → ≤⇒≤ᴸ (≤-reflexive (sym (iso» P γ)))
            }
