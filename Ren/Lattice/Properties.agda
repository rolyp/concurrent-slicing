-- Lattice analogues of certain Ren.Properties.
module Ren.Lattice.Properties where

   open import ConcurrentSlicingCommon

   open import Action using (Action)
   import Action.Lattice
   open import Action.Ren.Lattice renaming (_* to _ᴬ*̃)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; _+_)
   open import Name.Lattice as ᴺ̃ using (zero)
   open import Proc using (Proc)
   import Proc.Lattice
   open import Proc.Ren.Lattice renaming (
         _* to _*̃; *-preserves-≃ₑ to *̃-preserves-≃ₑ; *-preserves-∘ to *̃-preserves-∘; *-preserves-id to *̃-preserves-id
      )
   open import Ren as ᴿ using (Ren; +-preserves-involutivity); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃
      using (_ᴿ+_; to-↓; to-↓-preserves-≃ₑ; to-↓-preserves-+; suc; swap; push; id; pop; repl; weaken)
   open import Ren.Properties

   -- Should be able to generalise along the lines of Ren.Properties, but tricky.
   swap-involutivẽ : ∀ {Γ} {P : Proc (Γ + 2)} (P′ : ↓ P) → (swap *̃) ((swap *̃) P′) ≅ P′
   swap-involutivẽ P =
      let open ≅-Reasoning in
      begin
         (to-↓ ᴿ.swap *̃) ((to-↓ ᴿ.swap *̃) P)
      ≅⟨ *̃-preserves-∘ P ⟩
         (((to-↓ ᴿ.swap ᴿ̃.*) ∘ᶠ to-↓ ᴿ.swap) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (λ _ → ≡-to-≅ refl) P ⟩
         ((to-↓ (ᴿ.swap ∘ᶠ ᴿ.swap)) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (to-↓-preserves-≃ₑ swap-involutive) P ⟩
         (id *̃) P
      ≅⟨ *̃-preserves-id P ⟩
         P
      ∎

   swap+-involutivẽ : ∀ {Γ} Δ {P : Proc (Γ + 2 + Δ)} (P′ : ↓ P) → ((swap ᴿ+ Δ) *̃) (((swap ᴿ+ Δ) *̃) P′) ≅ P′
   swap+-involutivẽ Δ P =
      let open ≅-Reasoning in
      begin
         ((to-↓ ᴿ.swap ᴿ+ Δ) *̃) (((to-↓ ᴿ.swap ᴿ+ Δ) *̃) P)
      ≅⟨ ≅-cong ((to-↓ ᴿ.swap ᴿ+ Δ) *̃) (*̃-preserves-≃ₑ (≅-sym ∘ᶠ ≡-to-≅ ∘ᶠ to-↓-preserves-+ Δ ᴿ.swap) P) ⟩
         ((to-↓ ᴿ.swap ᴿ+ Δ) *̃) (((to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ)) *̃) P)
      ≅⟨ *̃-preserves-≃ₑ (≅-sym ∘ᶠ ≡-to-≅ ∘ᶠ to-↓-preserves-+ Δ ᴿ.swap) _ ⟩
         ((to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ)) *̃) (((to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ)) *̃) P)
      ≅⟨ *̃-preserves-∘ P ⟩
         ((((to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ)) ᴿ̃.*) ∘ᶠ (to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ))) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (λ x → ≅-refl) P ⟩
         ((to-↓ ((ᴿ.swap ᴿ.ᴿ+ Δ) ∘ᶠ (ᴿ.swap ᴿ.ᴿ+ Δ))) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (to-↓-preserves-≃ₑ (+-preserves-involutivity ᴿ.swap Δ swap-involutive)) P ⟩
         (to-↓ idᶠ *̃) P
      ≅⟨ *̃-preserves-id P ⟩
         P
      ∎

   -- More of the same; trivial but tedious, so leave for now. TODO: abstract over ↓ A for any Renameable A.
   postulate
      swap∘push∘push̃ : ∀ {Γ} {P : Proc Γ} (P′ : ↓ P) → (swap *̃) ((push *̃) ((push *̃) P′)) ≅ (push *̃) ((push *̃) P′)
      swap∘suc-swap∘swap̃ : ∀ {Γ} {P : Proc (Γ + 3)} (P′ : ↓ P) →
                           (swap {Γ + 1} *̃) ((suc swap *̃) ((swap *̃) P′)) ≅
                           (suc swap *̃) ((swap *̃) ((suc swap *̃) P′))
      pop∘push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc Γ} (P′ : ↓ P) → (pop y′ *̃) ((push *̃) P′) ≅ P′
      ᴬpop∘push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {a : Action Γ} (a′ : ↓ a) → (pop y′ ᴬ*̃) ((push ᴬ*̃) a′) ≅ a′
      swap∘suc-push̃ : ∀ {Γ} {P : Proc (Γ + 1)} (P′ : ↓ P) → (push *̃) P′ ≅ (swap *̃) ((suc push *̃) P′)
      swap∘push̃ : ∀ {Γ} {P : Proc (Γ + 1)} (P′ : ↓ P) → (suc push *̃) P′ ≅ (swap *̃) ((push *̃) P′)
      pop∘swap̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                  (suc (pop y′) *̃) P′ ≅ ((pop ((push ᴿ̃.*) y′)) *̃) ((swap *̃) P′)
      pop-swap̃ : ∀ {Γ} (y y′ : ↓ ᴺ.zero) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                  (pop y′ *̃) ((suc (repl y) *̃) ((swap {Γ} *̃) P′)) ≅ (pop y *̃) ((suc (repl y′) *̃) P′)
      pop∘suc-push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 1)} (P′ : ↓ P) →
                     (push *̃) ((pop y′ *̃) P′)≅ (pop ((push ᴿ̃.*) y′) *̃) ((suc push *̃) P′)
      swap-swap̃ : ∀ {Γ} {P P′ : Proc (Γ + 2)} {P† : ↓ P} {P‡ : ↓ P′} → (swap *̃) P† ≅ P‡ → P† ≅ (swap *̃) P‡

      -- Corresponds to id ∘ swap = swap ∘ id, which is too trivial to have a Ren.Properties counterpart.
      id-swap̃ : ∀ {Γ} (y : ↓ ᴺ.zero) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                    (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) P′) ≅ (swap *̃) ((suc (repl y) *̃) P′)
      -- Corresponds to id ∘ suc push ≡ swap ∘ push ∘ id, which we prove inline rather than as a lemma.
      id∘suc-push̃ : ∀ {Γ} {y : ↓ ᴺ.zero} {P : Proc (Γ + 1)} (P′ : ↓ P) →
                    (repl ((weaken ᴿ̃.*) y) *̃) ((suc push *̃) P′) ≅ (suc push *̃) ((repl y *̃) P′)
