-- Lattice analogues of certain Ren.Properties.
module Ren.Lattice.Properties where

   open import ConcurrentSlicingCommon

   open import Action using (Action)
   import Action.Lattice
   open import Action.Ren.Lattice renaming (_* to _ᴬ*̃)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; _+_)
   open import Proc using (Proc)
   import Proc.Lattice
   open import Proc.Ren.Lattice renaming (
         _* to _*̃; *-preserves-≃ₑ to *̃-preserves-≃ₑ; *-preserves-∘ to *̃-preserves-∘; *-preserves-id to *̃-preserves-id
      )
   open import Ren as ᴿ using (Ren; +-preserves-involutivity; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (_ᴿ+_; to-↓; to-↓-preserves-≃ₑ; to-↓-preserves-+)
   open import Ren.Properties

   -- Should be able to generalise along the lines of Ren.Properties, but tricky.
   swap-involutivẽ : ∀ {Γ} {P : Proc (Γ + 2)} (P′ : ↓ P) → (ᴿ̃.swap *̃) ((ᴿ̃.swap *̃) P′) ≅ P′
   swap-involutivẽ P =
      let open ≅-Reasoning in
      begin
         (to-↓ swap *̃) ((to-↓ swap *̃) P)
      ≅⟨ *̃-preserves-∘ P ⟩
         (((to-↓ swap ᴿ̃.*) ∘ᶠ to-↓ swap) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (λ _ → ≡-to-≅ refl) P ⟩
         ((to-↓ (swap ∘ᶠ swap)) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (to-↓-preserves-≃ₑ swap-involutive) P ⟩
         (ᴿ̃.id *̃) P
      ≅⟨ *̃-preserves-id P ⟩
         P
      ∎

   swap+-involutivẽ : ∀ {Γ} Δ {P : Proc (Γ + 2 + Δ)} (P′ : ↓ P) → ((ᴿ̃.swap ᴿ+ Δ) *̃) (((ᴿ̃.swap ᴿ+ Δ) *̃) P′) ≅ P′
   swap+-involutivẽ Δ P =
      let open ≅-Reasoning in
      begin
         ((to-↓ swap ᴿ+ Δ) *̃) (((to-↓ swap ᴿ+ Δ) *̃) P)
      ≅⟨ ≅-cong ((to-↓ swap ᴿ+ Δ) *̃) (*̃-preserves-≃ₑ (≅-sym ∘ᶠ ≡-to-≅ ∘ᶠ to-↓-preserves-+ Δ swap) P) ⟩
         ((to-↓ swap ᴿ+ Δ) *̃) (((to-↓ (swap ᴿ.ᴿ+ Δ)) *̃) P)
      ≅⟨ *̃-preserves-≃ₑ (≅-sym ∘ᶠ ≡-to-≅ ∘ᶠ to-↓-preserves-+ Δ swap) _ ⟩
         ((to-↓ (swap ᴿ.ᴿ+ Δ)) *̃) (((to-↓ (swap ᴿ.ᴿ+ Δ)) *̃) P)
      ≅⟨ *̃-preserves-∘ P ⟩
         ((((to-↓ (swap ᴿ.ᴿ+ Δ)) ᴿ̃.*) ∘ᶠ (to-↓ (swap ᴿ.ᴿ+ Δ))) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (λ x → ≅-refl) P ⟩
         ((to-↓ ((swap ᴿ.ᴿ+ Δ) ∘ᶠ (swap ᴿ.ᴿ+ Δ))) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (to-↓-preserves-≃ₑ (+-preserves-involutivity swap Δ swap-involutive)) P ⟩
         (to-↓ idᶠ *̃) P
      ≅⟨ *̃-preserves-id P ⟩
         P
      ∎

   -- More of the same; trivial but tedious, so leave for now. TODO: abstract over ↓ A for any Renameable A.
   postulate
      swap∘push∘push̃ : ∀ {Γ} {P : Proc Γ} (P′ : ↓ P) → (ᴿ̃.swap *̃) ((ᴿ̃.push *̃) ((ᴿ̃.push *̃) P′)) ≅ (ᴿ̃.push *̃) ((ᴿ̃.push *̃) P′)
      pop∘push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc Γ} (P′ : ↓ P) → (ᴿ̃.pop y′ *̃) ((ᴿ̃.push *̃) P′) ≅ P′
      ᴬpop∘push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {a : Action Γ} (a′ : ↓ a) → (ᴿ̃.pop y′ ᴬ*̃) ((ᴿ̃.push ᴬ*̃) a′) ≅ a′
      swap∘suc-push̃ : ∀ {Γ} {P : Proc (Γ + 1)} (P′ : ↓ P) → (ᴿ̃.push *̃) P′ ≅ (ᴿ̃.swap *̃) ((ᴿ̃.suc ᴿ̃.push *̃) P′)
      swap∘push̃ : ∀ {Γ} {P : Proc (Γ + 1)} (P′ : ↓ P) → (ᴿ̃.suc ᴿ̃.push *̃) P′ ≅ (ᴿ̃.swap *̃) ((ᴿ̃.push *̃) P′)
      pop∘swap̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                  (ᴿ̃.suc (ᴿ̃.pop y′) *̃) P′ ≅ ((ᴿ̃.pop ((ᴿ̃.push ᴿ̃.*) y′)) *̃) ((ᴿ̃.swap *̃) P′)
      pop∘suc-push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 1)} (P′ : ↓ P) →
                     (ᴿ̃.push *̃) ((ᴿ̃.pop y′ *̃) P′)≅ (ᴿ̃.pop ((ᴿ̃.push ᴿ̃.*) y′) *̃) ((ᴿ̃.suc ᴿ̃.push *̃) P′)
      swap-swap̃ : ∀ {Γ} {P P′ : Proc (Γ + 2)} {P† : ↓ P} {P‡ : ↓ P′} → (ᴿ̃.swap *̃) P† ≅ P‡ → P† ≅ (ᴿ̃.swap *̃) P‡
