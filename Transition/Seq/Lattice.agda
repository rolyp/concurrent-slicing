module Transition.Seq.Lattice where

   open import ConcurrentSlicingCommon

   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   open import Lattice using (Lattices; Prefixes); open Lattice.Prefixes ⦃...⦄
   open import Name using (_+_; +-assoc)
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Transition.Lattice as ᵀ̃ using (src; srcᴹ; tgt; tgtᴹ)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

   eq : ∀ Δ {Γ} (a⋆ : Action⋆ (Γ + Δ)) → Γ + Δ + inc⋆ a⋆ ≡ Γ + (Δ + inc⋆ a⋆)
   eq Δ {Γ} = +-assoc Γ Δ ∘ᶠ inc⋆

   quib : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (_ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → ↓ (Proc↱ (eq Δ a⋆) R)
   quib Δ {a⋆ = a⋆} {R} _ = ≅-subst✴ Proc ↓_ (eq Δ a⋆) (≅-sym (Proc↲ (eq Δ a⋆) R))

   quib-removable : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → R′ ≅ quib Δ E⋆ R′
   quib-removable Δ {a⋆ = a⋆} {R} _ = ≅-sym ∘ᶠ ≅-subst✴-removable Proc ↓_ (eq Δ a⋆) (≅-sym (Proc↲ (eq Δ a⋆) R))

   bibble : ∀ {Γ Γ′} {P₀ : Proc Γ} {Q₀ : Proc Γ′} {P P′ : ↓ P₀} {Q Q′ : ↓ Q₀} →
            Γ ≡ Γ′ → P₀ ≅ Q₀ → P ≅ Q → P′ ≅ Q′ → P ≤ P′ → Q ≤ Q′
   bibble refl ≅-refl ≅-refl ≅-refl = idᶠ

   src⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓ R → ↓ P
   src⋆ [] P = P
   src⋆ {Γ} {a⋆ = _ ᵇ∷ a⋆} (E ᵇ∷ E⋆) R =
      src E (src⋆ E⋆ (≅-subst✴ Proc ↓_ (sym (+-assoc Γ 1 (inc⋆ a⋆))) (Proc↲ (+-assoc Γ 1 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆)) R))
   src⋆ {Γ} {a⋆ = _ ᶜ∷ a⋆} (E ᶜ∷ E⋆) R =
      src E (src⋆ E⋆ (≅-subst✴ Proc ↓_ (sym (+-assoc Γ 0 (inc⋆ a⋆))) (Proc↲ (+-assoc Γ 0 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆)) R))

   tgt⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓ P → ↓ R
   tgt⋆ [] R = R
   tgt⋆ {Γ} {a⋆ = _ ᵇ∷ a⋆} (E ᵇ∷ E⋆) P =
      ≅-subst✴ Proc ↓_ (+-assoc Γ 1 (inc⋆ a⋆)) (≅-sym (Proc↲ (+-assoc Γ 1 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆))) (tgt⋆ E⋆ (tgt E P))
   tgt⋆ {Γ} {a⋆ = _ ᶜ∷ a⋆} (E ᶜ∷ E⋆) P =
      ≅-subst✴ Proc ↓_ (+-assoc Γ 0 (inc⋆ a⋆)) (≅-sym (Proc↲ (+-assoc Γ 0 (inc⋆ a⋆)) (ᵀ⋆.tgt⋆ E⋆))) (tgt⋆ E⋆ (tgt E P))

   tgt⋆ᴹ : ∀ {Γ P₀} {a⋆ : Action⋆ Γ} {R} (E⋆ : P₀ —[ a⋆ ]→⋆ R) {P P′ : ↓ P₀} → P ≤ P′ → tgt⋆ E⋆ P ≤ tgt⋆ E⋆ P′
   tgt⋆ᴹ [] P = P
   tgt⋆ᴹ {a⋆ = _ ᵇ∷ a⋆} (E ᵇ∷ E⋆) {P} {P′} P† =
      bibble (eq 1 a⋆) (≅-sym (Proc↲ (eq 1 a⋆) (ᵀ⋆.tgt⋆ E⋆)))
         (quib-removable 1 E⋆ (tgt⋆ E⋆ (tgt E P)))
         (quib-removable 1 E⋆ (tgt⋆ E⋆ (tgt E P′)))
         (tgt⋆ᴹ E⋆ (tgtᴹ E P†))
   tgt⋆ᴹ {a⋆ = _ ᶜ∷ a⋆} (E ᶜ∷ E⋆) {P} {P′} P† =
      bibble (eq 0 a⋆) (≅-sym (Proc↲ (eq 0 a⋆) (ᵀ⋆.tgt⋆ E⋆)))
         (quib-removable 0 E⋆ (tgt⋆ E⋆ (tgt E P)))
         (quib-removable 0 E⋆ (tgt⋆ E⋆ (tgt E P′)))
         (tgt⋆ᴹ E⋆ (tgtᴹ E P†))
