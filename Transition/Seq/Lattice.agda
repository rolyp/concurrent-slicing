module Transition.Seq.Lattice where

   open import ConcurrentSlicingCommon

   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   open import Lattice using (Lattices; Prefixes); open Lattice.Prefixes ⦃...⦄ using (↓_)
   open import Name using (+-assoc)
   open import Proc using (Proc; Proc↲)
   open import Transition.Lattice as ᵀ̃ using (src; tgt)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

   src⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓ R → ↓ P
   src⋆ [] P = P
   src⋆ {Γ} {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) R =
      src E (src⋆ E⋆ (≅-subst✴ Proc ↓_ (sym (+-assoc Γ 1 (inc⋆ a⋆))) (Proc↲ (+-assoc Γ 1 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆)) R))
   src⋆ {Γ} {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) R =
      src E (src⋆ E⋆ (≅-subst✴ Proc ↓_ (sym (+-assoc Γ 0 (inc⋆ a⋆))) (Proc↲ (+-assoc Γ 0 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆)) R))

   tgt⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓ P → ↓ R
   tgt⋆ [] R = R
   tgt⋆ {Γ} {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) P =
      ≅-subst✴ Proc ↓_ (+-assoc Γ 1 (inc⋆ a⋆)) (≅-sym (Proc↲ (+-assoc Γ 1 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆))) (tgt⋆ E⋆ (tgt E P))
   tgt⋆ {Γ} {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) P =
      ≅-subst✴ Proc ↓_ (+-assoc Γ 0 (inc⋆ a⋆)) (≅-sym (Proc↲ (+-assoc Γ 0 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆))) (tgt⋆ E⋆ (tgt E P))
