-- Lattice analogues of certain Ren.Properties.
module Ren.Lattice.Properties where

   open import ConcurrentSlicingCommon

   open import Name as ᴺ using (_+_)
   open import Proc using (Proc)
   open import Proc.Lattice using (↓_)
   open import Proc.Ren.Lattice using (_*; *-preserves-≃ₑ; *-preserves-∘; *-preserves-id)
   open import Ren as ᴿ using ()
   open import Ren.Properties
   open import Ren.Lattice as ᴿ̃ using (to-↓; to-↓-preserves-≃ₑ)

   swap̃-involutive : ∀ {Γ} {P : Proc (Γ + 2)} (P′ : ↓ P) → (ᴿ̃.swap *) ((ᴿ̃.swap *) P′) ≅ P′
   swap̃-involutive {P = P₀} P =
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
