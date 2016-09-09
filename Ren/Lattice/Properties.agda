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
      using (_̃_; _ᴿ+_; to-↓; to-↓-preserves-≃ₑ; to-↓-preserves-+; suc; swap; push; id; repl; pop; weaken)
   open import Ren.Properties

   -- Should be able to generalise along the lines of Ren.Properties, but tricky.
   swap-involutivẽ : ∀ {Γ} {P : Proc (Γ + 2)} (P′ : ↓ P) → (swap *̃) ((swap *̃) P′) ≅ P′
   swap-involutivẽ P =
      let open ≅-Reasoning in
      begin
         (to-↓ ᴿ.swap *̃) ((to-↓ ᴿ.swap *̃) P)
      ≅⟨ *̃-preserves-∘ P ⟩
         (((_̃_ (to-↓ ᴿ.swap)) ∘ᶠ to-↓ ᴿ.swap) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (λ _ → ≡-to-≅ refl) P ⟩
         ((to-↓ (ᴿ.swap ∘ᶠ ᴿ.swap)) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (to-↓-preserves-≃ₑ ᴿ.swap-involutive) P ⟩
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
         (((_̃_ (to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ))) ∘ᶠ (to-↓ (ᴿ.swap ᴿ.ᴿ+ Δ))) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (λ x → ≅-refl) P ⟩
         ((to-↓ ((ᴿ.swap ᴿ.ᴿ+ Δ) ∘ᶠ (ᴿ.swap ᴿ.ᴿ+ Δ))) *̃) P
      ≅⟨ *̃-preserves-≃ₑ (to-↓-preserves-≃ₑ (+-preserves-involutivity ᴿ.swap Δ ᴿ.swap-involutive)) P ⟩
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
      pop∘suc-push̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 1)} (P′ : ↓ P) →
                     (push *̃) ((pop y′ *̃) P′) ≅ (pop (push ̃ y′) *̃) ((suc push *̃) P′)
      pop-zero∘suc-push̃ : ∀ {Γ} (y : ↓ ᴺ.zero) {P : Proc (Γ + 1)} (P′ : ↓ P) →
                           (pop {Γ + 1} y *̃) ((suc push *̃) P′) ≅ (repl y *̃) P′
      pop-pop-swap̃ : ∀ {Γ} {x y : Name Γ} (x′ : ↓ x) (y′ : ↓ y) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                      (pop x′ *̃) ((suc (pop y′) *̃) ((swap {Γ} *̃) P′)) ≅ (pop y′ *̃) ((suc (pop x′) *̃) P′)
      pop∘swap̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                  (suc (pop y′) *̃) P′ ≅ ((pop (push ̃ y′)) *̃) ((swap *̃) P′)
      suc-pop∘swap̃ : ∀ {Γ} {y : Name Γ} (y′ : ↓ y) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                      (suc (pop y′) *̃) ((swap *̃) P′) ≅ (pop (push ̃ y′) *̃) P′
      swap-swap̃ : ∀ {Γ} {P P′ : Proc (Γ + 2)} {P† : ↓ P} {P‡ : ↓ P′} → (swap *̃) P† ≅ P‡ → P† ≅ (swap *̃) P‡

      -- Some id-related properties which become non-trivial in the presence of slicing; sanity-checked
      -- on paper using string diagrams.

      -- Corresponds to id ∘ swap = swap ∘ id.
      id-swap-id̃ : ∀ {Γ} (y : ↓ ᴺ.zero) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                    (repl (weaken ̃ y) *̃) ((swap *̃) P′) ≅ (swap *̃) ((suc (repl y) *̃) P′)
      -- Corresponds to id ∘ suc id ∘ swap = swap ∘ id ∘ suc id.
      id-suc-id-swap-id-suc-id̃ : ∀ {Γ} (y y′ : ↓ ᴺ.zero) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                                  (repl (weaken ̃ y′) *̃) ((suc (repl y) *̃) ((swap *̃) P′)) ≅
                                  (swap *̃) ((repl (weaken ̃ y) *̃) ((suc (repl y′) *̃) P′))
      -- Corresponds to id ∘ suc push ≡ suc push ∘ id.
      id-suc-push-id̃ : ∀ {Γ} (y : ↓ ᴺ.zero) {P : Proc (Γ + 1)} (P′ : ↓ P) →
                        (repl (weaken ̃ y) *̃) ((suc push *̃) P′) ≅ (suc push *̃) ((repl y *̃) P′)
      -- Corresponds to id ∘ pop (push y) ≡ pop (push y) ∘ id.
      id-pop-push-id̃ : ∀ {Γ} {y : Name Γ} (y† : ᴺ̃.↓ y) (y‡ : ᴺ̃.↓_ {ᴺ.suc Γ} ᴺ.zero) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                        (repl y‡ *̃) ((pop (push ̃ y†) *̃) P′) ≅ (pop (push ̃ y†) *̃) ((suc (repl y‡) *̃) P′)

      -- Corresponds to pop zero ∘ swap = pop zero
      id-pop-swap̃ : ∀ {Γ} (y y′ : ↓ ᴺ.zero) {P : Proc (Γ + 2)} (P′ : ↓ P) →
                     (pop y *̃) ((suc (repl y′) *̃) ((swap *̃) P′)) ≅ (pop y′ *̃) ((suc (repl y) *̃) P′)
