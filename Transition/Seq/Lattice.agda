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

   adjust : ∀ Δ {Γ} (a⋆ : Action⋆ (Γ + Δ)) {R : Proc (Γ + Δ + inc⋆ a⋆)} (R′ : ↓ R) → ↓ (Proc↱ (eq Δ a⋆) R)
   adjust Δ a⋆ {R} = ≅-subst✴ Proc ↓_ (eq Δ a⋆) (≅-sym (Proc↲ (eq Δ a⋆) R))

   sym-adjust : ∀ Δ {Γ} (a⋆ : Action⋆ (Γ + Δ)) {R} (R′ : ↓ (Proc↱ (eq Δ a⋆) R)) → ↓ R
   sym-adjust Δ a⋆ {R} = ≅-subst✴ Proc ↓_ (sym (eq Δ a⋆)) (Proc↲ (eq Δ a⋆) R)

   adjust-removable : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → R′ ≅ adjust Δ a⋆ R′
   adjust-removable Δ {a⋆ = a⋆} {R} _ = ≅-sym ∘ᶠ ≅-subst✴-removable Proc ↓_ (eq Δ a⋆) (≅-sym (Proc↲ (eq Δ a⋆) R))

   sym-adjust-removable : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (E⋆ : P —[ a⋆ ]→⋆ R)
                          (R′ : ↓ (Proc↱ (eq Δ a⋆) R)) → R′ ≅ sym-adjust Δ a⋆ R′
   sym-adjust-removable Δ {a⋆ = a⋆} {R} _ = ≅-sym ∘ᶠ ≅-subst✴-removable Proc ↓_ (sym (eq Δ a⋆)) (Proc↲ (eq Δ a⋆) R)

   ≤-preserves-≅ : ∀ {Γ Γ′} {P₀ : Proc Γ} {Q₀ : Proc Γ′} {P P′ : ↓ P₀} {Q Q′ : ↓ Q₀} →
                   Γ ≡ Γ′ → P₀ ≅ Q₀ → P ≅ Q → P′ ≅ Q′ → P ≤ P′ → Q ≤ Q′
   ≤-preserves-≅ refl ≅-refl ≅-refl ≅-refl = idᶠ

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
      ≤-preserves-≅ (eq 1 a⋆) (≅-sym (Proc↲ (eq 1 a⋆) (ᵀ⋆.tgt⋆ E⋆)))
         (adjust-removable 1 E⋆ (tgt⋆ E⋆ (tgt E P)))
         (adjust-removable 1 E⋆ (tgt⋆ E⋆ (tgt E P′)))
         (tgt⋆ᴹ E⋆ (tgtᴹ E P†))
   tgt⋆ᴹ {a⋆ = _ ᶜ∷ a⋆} (E ᶜ∷ E⋆) {P} {P′} P† =
      ≤-preserves-≅ (eq 0 a⋆) (≅-sym (Proc↲ (eq 0 a⋆) (ᵀ⋆.tgt⋆ E⋆)))
         (adjust-removable 0 E⋆ (tgt⋆ E⋆ (tgt E P)))
         (adjust-removable 0 E⋆ (tgt⋆ E⋆ (tgt E P′)))
         (tgt⋆ᴹ E⋆ (tgtᴹ E P†))

   src⋆ᴹ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R₀} (E⋆ : P —[ a⋆ ]→⋆ R₀) {R R′ : ↓ R₀} → R ≤ R′ → src⋆ E⋆ R ≤ src⋆ E⋆ R′
   src⋆ᴹ [] R = R
   src⋆ᴹ {a⋆ = _ ᵇ∷ a⋆} (E ᵇ∷ E⋆) {R} {R′} R† =
      srcᴹ E (src⋆ᴹ E⋆ (≤-preserves-≅ (sym (eq 1 a⋆))
         (Proc↲ (eq 1 a⋆) (ᵀ⋆.tgt⋆ E⋆)) (sym-adjust-removable 1 E⋆ R) (sym-adjust-removable 1 E⋆ R′) R†))
   src⋆ᴹ {a⋆ = _ ᶜ∷ a⋆} (E ᶜ∷ E⋆) {R} {R′} R† =
      srcᴹ E (src⋆ᴹ E⋆ (≤-preserves-≅ (sym (eq 0 a⋆))
         (Proc↲ (eq 0 a⋆) (ᵀ⋆.tgt⋆ E⋆)) (sym-adjust-removable 0 E⋆ R) (sym-adjust-removable 0 E⋆ R′) R†))
