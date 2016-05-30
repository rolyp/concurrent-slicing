module Transition.Concur.Cofinal.Lattice.Helpers where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Ren.Lattice renaming (_* to _ᴬ*̃)
   open import Braiding.Proc.Lattice using (braid̂)
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; Cxt; _+_)
   open import Name.Lattice as ᴺ̃ using (); open ᴺ̃.↓_
   open import Proc as ᴾ using (Proc; Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   open import Proc.Ren.Lattice using () renaming (_* to _*̃)
   open import Ren as ᴿ using (); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (swap; pop; push; _ᴿ+_; suc)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ⊖₁)
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁)
   open import Transition.Lattice using (target; action)
   open import Transition.Ren using (_*ᵇ; _*ᶜ)
   open import Transition.Ren.Lattice using (renᵇ-target-comm; renᵇ-action-comm; renᶜ-target-comm; renᶜ-action-comm)

   open Delta′

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) → ↓ P → ↓ P′
   braiding ˣ∇ˣ eq rewrite eq = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   -- Helpers arise from need to pattern-match on an equality to get braiding to reduce.
   reduce-ˣ∇ˣ : ∀ {Γ P P′} {x u : Name Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ˣ∇ˣ {x = x} {u}) {0} γ P† ≅ P†
   reduce-ˣ∇ˣ refl _ = ≅-refl

   reduce-ᵇ∇ᵇ : ∀ {Γ P P′} {a a′ : Actionᵇ Γ} (γ : ((ᴿ.swap ᴿ.ᴿ+ 0) *) P ≡ P′) (P† : ↓ P) →
                braiding (ᵇ∇ᵇ {a = a} {a′}) {0} γ P† ≅ ((swap ᴿ+ 0) *̃) P†
   reduce-ᵇ∇ᵇ refl _ = ≅-refl

   reduce-ᵇ∇ᶜ : ∀ {Γ P P′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᵇ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᵇ∇ᶜ refl _ = ≅-refl

   reduce-ᶜ∇ᵇ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᶜ∇ᵇ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᶜ∇ᵇ refl _ = ≅-refl

   reduce-ᶜ∇ᶜ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᶜ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᶜ∇ᶜ refl _ = ≅-refl

   ◻-cong : ∀ {Γ} {P₀ P₁ : Proc Γ} → P₀ ≡ P₁ →
            _≅_ {A = ↓_ {A = Proc Γ} _} (◻ {P = P₀}) {↓_ {A = Proc Γ} _} (◻ {P = P₁})
   ◻-cong refl = ≅-refl

   [-│]-cong : ∀ {Γ} {P₀ P₁ Q₀ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₁} (Q : ↓ Q₀) → P₀ ≡ P₁ → P ≅ P′ →
               _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P′ │ Q ]
   [-│]-cong _ refl ≅-refl = ≅-refl

   [│-]-cong : ∀ {Γ} {P₀ Q₀ Q₁ : Proc Γ} (P : ↓ P₀) {Q : ↓ Q₀} {Q′ : ↓ Q₁} → Q₀ ≡ Q₁ → Q ≅ Q′ →
               _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P │ Q′ ]
   [│-]-cong _ refl ≅-refl = ≅-refl

   [-│-]-cong : ∀ {Γ} {P₀ P₁ Q₀ Q₁ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₁} {Q : ↓ Q₀} {Q′ : ↓ Q₁} →
                P₀ ≡ P₁ → P ≅ P′ → Q₀ ≡ Q₁ → Q ≅ Q′ →
                _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P′ │ Q′ ]
   [-│-]-cong refl ≅-refl refl ≅-refl = ≅-refl

   ᴬgamma₁-│•ᵇ : ∀ {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᵇ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ (x •) ᵇ - _ ]→ R′₀}
                (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (R′ : ↓ R′₀) →
                target E′ P ≡ R′ → action (E/E′ (⊖₁ 𝐸)) (target E′ P) ≡ (push ᴬ*̃) (action E P) →
                let pop-y*E/E′ = subst (λ a → _ —[ a ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸)))
                                       (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) in
                action pop-y*E/E′ ((pop ◻ *̃) R′) ≡ action E P
   ᴬgamma₁-│•ᵇ {Γ} {x = x} {y} {a = a} {E} {E′} 𝐸 F P R′ ≡R′ IH = ≅-to-≡ (
      let T : Actionᵇ Γ → Set
          T = λ a′ → (ᴿ.pop y *) (ᵀ.target E′) —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸))
          pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸)))
          open ≅-Reasoning in
      begin
         action pop-y*E/E′  ((pop ◻ *̃) R′)
      ≅⟨ ≅-cong✴ T (sym (pop∘push y a)) (λ E† → action E† ((pop ◻ *̃) R′)) (≡-subst-removable T (pop∘push y a) _) ⟩
         action ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) ((pop ◻ *̃) R′)
      ≡⟨ sym (renᵇ-action-comm (E/E′ (⊖₁ 𝐸)) (pop ◻) R′) ⟩
         (pop {x₀ = y} ◻ ᴬ*̃) (action (E/E′ (⊖₁ 𝐸)) R′)
      ≡⟨ cong ((pop {x₀ = y} ◻ ᴬ*̃) ∘ᶠ action (E/E′ (⊖₁ 𝐸))) (sym ≡R′) ⟩
         (pop {x₀ = y} ◻ ᴬ*̃) (action (E/E′ (⊖₁ 𝐸)) (target E′ P))
      ≡⟨ cong (pop {x₀ = y} ◻ ᴬ*̃) IH ⟩
         (pop {x₀ = y} ◻ ᴬ*̃) ((push ᴬ*̃) (action E P))
      ≅⟨ ᴬpop∘push̃ ◻ (action E P) ⟩
         action E P
      ∎)

   gamma₁-│•ᵇ : ∀ {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᵇ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ (x •) ᵇ - _ ]→ R′₀}
               (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀) (S† : ↓ (ᴿ.push *) S₀)
               (S‡ : ↓ S₀) (R′ : ↓ R′₀) (P′ : ↓ S (⊖₁ 𝐸)) (y† : ↓ ᴺ.suc y) (y‡ : ↓ y) →
               target E′ P ≡ R′ → target (E′/E (⊖₁ 𝐸)) (target E P) ≡ P′ →
               target ((ᴿ.push *ᶜ) F) ((push *̃) Q) ≡ S† → target F Q ≡ S‡ → y† ≡ (push ᴿ̃.*) y‡ →
               braiding (ᵇ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (target (E′/E (⊖₁ 𝐸)) (target E P)) ≡
               target (E/E′ (⊖₁ 𝐸)) (target E′ P) →
               let α : (ᴿ.pop (ᴺ.suc y) *) (S (⊖₁ 𝐸)) ≡ (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸))
                   α = let open EqReasoning (setoid _) in
                      begin
                         (ᴿ.pop (ᴺ.suc y) *) (S (⊖₁ 𝐸))
                      ≡⟨ cong (ᴿ.pop (ᴺ.suc y) *) (swap-swap (γ₁ 𝐸)) ⟩
                         (ᴿ.pop (ᴺ.suc y) *) ((ᴿ.swap *) (S′ (⊖₁ 𝐸)))
                      ≡⟨ sym (pop∘swap y _) ⟩
                         (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸))
                      ∎
                   pop-y*E/E′ = subst (λ a → _ —[ a ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸)))
                                      (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) in
               braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ α refl)
                        [ (pop y† *̃) P′ │ S† ] ≡
               [ target pop-y*E/E′ ((pop y‡ *̃) R′) │ ((push *̃) S‡) ]
   gamma₁-│•ᵇ {Γ} {x = x} {y} {a = a} {E} {E′} 𝐸 F P Q S† S‡ R′ P′ y† y‡ ≡R′ ≡P′ ≡S† ≡S‡ ≡y† IH =
      let T : Actionᵇ Γ → Set
          T = λ a′ → (ᴿ.pop y *) (ᵀ.target E′) —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸))
          pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸)))
          P″ = target (E/E′ (⊖₁ 𝐸)) R′
          α : (ᴿ.pop (ᴺ.suc y) *) (S (⊖₁ 𝐸)) ≡ (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸))
          α = let open EqReasoning (setoid _) in
             begin
                (ᴿ.pop (ᴺ.suc y) *) (S (⊖₁ 𝐸))
             ≡⟨ cong (ᴿ.pop (ᴺ.suc y) *) (swap-swap (γ₁ 𝐸)) ⟩
                (ᴿ.pop (ᴺ.suc y) *) ((ᴿ.swap *) (S′ (⊖₁ 𝐸)))
             ≡⟨ sym (pop∘swap y _) ⟩
                (ᴿ.suc (ᴿ.pop y) *) (S′ (⊖₁ 𝐸))
             ∎
          β : (swap *̃) P′ ≅ P″
          β = let open ≅-Reasoning in
             begin
                (swap *̃) P′
             ≡⟨ cong (swap *̃) (sym ≡P′) ⟩
                (swap *̃) (target (E′/E (⊖₁ 𝐸)) (target E P))
             ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) ⟩
                braiding (ᵇ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (target (E′/E (⊖₁ 𝐸)) (target E P))
             ≡⟨ IH ⟩
                target (E/E′ (⊖₁ 𝐸)) (target E′ P)
             ≡⟨ cong (target (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                P″
             ∎
          δ : (pop y† *̃) P′ ≅ target pop-y*E/E′ (((pop y‡) *̃) R′)
          δ = let open ≅-Reasoning in
             begin
                (pop y† *̃) P′
             ≅⟨ ≅-cong✴ ↓_ (swap-swap (γ₁ 𝐸)) (pop y† *̃) (swap-swap̃ β) ⟩
                (pop y† *̃) ((swap *̃) P″)
             ≡⟨ cong (λ y → (pop y *̃) ((swap *̃) P″)) ≡y† ⟩
                (pop ((push ᴿ̃.*) y‡) *̃) ((swap *̃) P″)
             ≅⟨ ≅-sym (pop∘swap̃ y‡ P″) ⟩
                (suc (pop y‡) *̃) P″
             ≡⟨ renᵇ-target-comm (E/E′ (⊖₁ 𝐸)) (pop y‡) R′ ⟩
                target (((ᴿ.pop y) *ᵇ) (E/E′ (⊖₁ 𝐸))) (((pop y‡) *̃) R′)
             ≅⟨ ≅-cong✴ T (pop∘push y a) (λ E† → target E† ((pop y‡ *̃) R′))
                        (≅-sym (≡-subst-removable T (pop∘push y a) _)) ⟩
                target pop-y*E/E′ (((pop y‡) *̃) R′)
             ∎ in ≅-to-≡ (
      let open ≅-Reasoning in
      begin
         braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ α refl) [ (pop y† *̃) P′ │ S† ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ α refl) _ ⟩
         [ (pop y† *̃) P′ │ S† ]
      ≅⟨ [-│-]-cong α δ refl (≡-to-≅ (trans (sym ≡S†) (trans (sym (renᶜ-target-comm F push Q))
                                                             (cong (push *̃) ≡S‡)))) ⟩
         [ target pop-y*E/E′ ((pop y‡ *̃) R′) │ (push *̃) S‡ ]
      ∎)

   postulate
      gamma₁-νᵛᵛ : ∀ {Γ} {P₀ : Proc (Γ + 1)} {R₀ R′₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ τ ᶜ - _ ]→ R′₀}
                  (𝐸 : E ⌣₁[ ᵛ∇ᵛ ] E′) (S† : ↓ S (⊖₁ 𝐸)) (S‡ : ↓ S′ (⊖₁ 𝐸)) →
                  _≡_ {A = ↓_ {A = Proc Γ} (ν Proc↱ refl (S′ (⊖₁ 𝐸)))} [ ν braid̂ (γ₁ 𝐸) S† ] [ ν S‡ ]
--    gamma₁-νᵛᵛ = {!!}
