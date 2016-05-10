-- Lattice analogues of certain Ren.Properties.
module Ren.Lattice.Properties where

   open import ConcurrentSlicingCommon

   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (_+_)
   open import Proc using (Proc)
   import Proc.Lattice
   open import Proc.Ren.Lattice using (_*; *-preserves-≃ₑ; *-preserves-∘; *-preserves-id)
   open import Ren as ᴿ using (Ren)
   open import Ren.Lattice as ᴿ̃ using (_ᴿ+_; to-↓; to-↓-preserves-≃ₑ)
   open import Ren.Properties

   -- Should be able to generalise along the lines of Ren.Properties, but a bit tricky.
   swap̃-involutive : ∀ {Γ} {P : Proc (Γ + 2)} (P′ : ↓ P) → (ᴿ̃.swap *) ((ᴿ̃.swap *) P′) ≅ P′
   swap̃-involutive P =
      let open ≅-Reasoning in
      begin
         (ᴿ̃.swap *) ((ᴿ̃.swap *) P)
      ≅⟨ *-preserves-∘ P ⟩
         (((ᴿ̃.swap ᴿ̃.*) ∘ᶠ ᴿ̃.swap) *) P
      ≅⟨ *-preserves-≃ₑ (λ _ → ≡-to-≅ refl) P ⟩
         ((to-↓ (ᴿ.swap ∘ᶠ ᴿ.swap)) *) P
      ≅⟨ *-preserves-≃ₑ (to-↓-preserves-≃ₑ swap-involutive) P ⟩
         (ᴿ̃.id *) P
      ≅⟨ *-preserves-id P ⟩
         P
      ∎

   postulate
      swap̃+-involutive : ∀ {Γ} Δ {P : Proc (Γ + 2 + Δ)} (P′ : ↓ P) → ((ᴿ̃.swap ᴿ+ Δ) *) (((ᴿ̃.swap ᴿ+ Δ) *) P′) ≅ P′
