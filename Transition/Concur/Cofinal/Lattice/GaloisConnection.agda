module Transition.Concur.Cofinal.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⌣-sym)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (Cxt; zero)
   open import Proc as ᴾ using (Proc↱)
   import Proc.Lattice
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur; ⌣-sym; module Delta′; ⊖); open Delta′
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; ⋈̂-sym)
   open import Transition.Concur.Cofinal.Lattice using (braiding)

   braidingᴹ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P₀ P′₀} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P₀ P′₀) →
               ∀ {P P′ : ↓ P₀} → P ≤ P′ → braiding 𝑎 γ P ≤ braiding 𝑎 γ P′
   braidingᴹ = {!!}

   «iso : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) (P† : ↓ P) →
          braiding 𝑎 (⋈̂-sym 𝑎 Δ γ) (braiding 𝑎 γ P†) ≡ P†
   «iso P = {!!}

   iso» : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) (P† : ↓ P′) →
          braiding 𝑎 γ (braiding 𝑎 (⋈̂-sym 𝑎 Δ γ) P†) ≡ P†
   iso» 𝑎 γ P = {!!}

   gc : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) →
        GaloisConnection (poset {a = P}) (poset {a = P′})
   gc 𝑎 {Δ} γ = ⟪ braiding 𝑎 γ , braiding 𝑎 (⋈̂-sym 𝑎 Δ γ) ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braidingᴹ 𝑎 γ ∘ᶠ ≤ᴸ⇒≤;
               g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braidingᴹ 𝑎 (⋈̂-sym 𝑎 Δ γ) ∘ᶠ ≤ᴸ⇒≤;
               g∘f≤id = λ P → ≤⇒≤ᴸ (≤-reflexive («iso 𝑎 γ P));
               id≤f∘g = λ P → ≤⇒≤ᴸ (≤-reflexive (sym (iso» 𝑎 γ P)))
            }
