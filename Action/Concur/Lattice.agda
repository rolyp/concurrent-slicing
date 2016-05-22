module Action.Concur.Lattice where

   open import ConcurrentSlicingCommon

   open import Action using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖); open _ᴬ⌣_
   open import Action.Lattice as ᴬ̃ using (); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name.Lattice as ᴺ̃ using (suc; zero)
   open import Ren.Lattice using (push)

   -- Need more consistent naming here. Lattice counterpart of ᴬ/.
   residual : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → ↓ a′ → ↓ π₁ (ᴬ⊖ a⌣a′)
   residual _ ◻ = ◻
   residual ˣ∇ˣ [ (• x) ᵇ ] = [ • suc x 〈 zero 〉 ᶜ ]
   residual ᵇ∇ᵇ [ (x •) ᵇ ] = [ {!!} ]
   residual ᵇ∇ᵇ [ (• x) ᵇ ] = {!!}
   residual ᵇ∇ᶜ [ a ᶜ ] = [ {!!} ]
   residual ᶜ∇ᵇ [ a ᵇ ] = [ a ᵇ ]
   residual ᶜ∇ᶜ [ a ] = [ a ]
   residual ᵛ∇ᵛ [ τ ᶜ ] = [ τ ᶜ ]
