module Transition.Concur.Cofinal.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖-✓)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (zero)
   open import Proc as ᴾ using (Proc↱)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur; ⌣-sym; module Delta′; ⊖); open Delta′
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; ⋈̂-sym)
   open import Transition.Concur.Cofinal.Lattice using (braiding)

   -- Exhibit one half of the isomorphism and then derive the other from involutivity of symmetry.
   iso» : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣[ 𝑎 ] E′) → let Q₀ = S (⊖ 𝐸); Q₀′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖ 𝐸))) in
          (γ : ⋈̂[ Γ , 𝑎 , zero ] Q₀ Q₀′) (Q : ↓ Q₀) → braiding 𝐸 γ (braiding ? (⋈̂-sym ? ? ? γ) Q) ≡ ?
   iso» P = ?

   gc : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
        (𝐸 : E ⌣[ 𝑎 ] E′) → let Q = S (⊖ 𝐸); Q′ = (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖ 𝐸))) in
        (γ : ⋈̂[ Γ , 𝑎 , zero ] Q Q′) → GaloisConnection (poset {a = Q}) (poset {a = Q′})
   gc 𝐸 γ = ⟪ braiding 𝐸 γ , braiding (⌣-sym 𝐸) (⋈̂-sym ? ? ? γ) ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ _ _ → ?; -- -≤⇒≤ᴸ ∘ᶠ braiding 𝐸 γ ∘ᶠ ?≤ᴸ⇒≤-
               g-mono = λ _ _ → ?; -- ≤⇒≤ᴸ ∘ᶠ braiding (⋈̂-sym γ) ∘ᶠ ≤ᴸ⇒≤;
               g∘f≤id = λ P → ≤⇒≤ᴸ (≤-reflexive ?);
               id≤f∘g = λ P → ≤⇒≤ᴸ ? -- (≤-reflexive (sym (iso» P γ)))
            }
