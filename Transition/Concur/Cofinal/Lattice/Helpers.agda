module Transition.Concur.Cofinal.Lattice.Helpers where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   import Name as ᴺ
   import Ren as ᴿ
   import Ren.Lattice as ᴿ̃
   open import Transition.Concur.Cofinal.Lattice.Common

{-
   gamma₁-│•ᵇ : ∀ {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᵇ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ (x •) ᵇ - _ ]→ R′₀}
                (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀) (S† : ↓ (ᴿ.push *) S₀)
                (S‡ : ↓ S₀) (R′ : ↓ R′₀) (P′ : ↓ tgt₁ (⊖₁ 𝐸)) (y† : ↓ ᴺ.suc y) (y‡ : ↓ y) →
                tgt E′ P ≡ R′ → tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′ →
                tgt ((ᴿ.push *ᶜ) F) ((push *̃) Q) ≡ S† → tgt F Q ≡ S‡ → y† ≡ (push ᴿ̃.*) y‡ →
                braiding (ᵇ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
                tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
                let α : (ᴿ.pop (ᴺ.suc y) *) (tgt₁ (⊖₁ 𝐸)) ≡ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
                    α = let open EqReasoning (setoid _) in
                       begin
                          (ᴿ.pop (ᴺ.suc y) *) (tgt₁ (⊖₁ 𝐸))
                       ≡⟨ cong (ᴿ.pop (ᴺ.suc y) *) (swap-swap (γ₁ 𝐸)) ⟩
                          (ᴿ.pop (ᴺ.suc y) *) ((ᴿ.swap *) (tgt₂ (⊖₁ 𝐸)))
                       ≡⟨ sym (pop∘swap y _) ⟩
                          (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
                       ∎
                    T : Actionᵇ Γ → Set
                    T = λ a′ → (ᴿ.pop y *) (ᵀ.tgt E′) —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
                    pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) in
                braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ α refl)
                [ (pop y† *̃) P′ │ S† ] ≡
                [ tgt pop-y*E/E′ ((pop y‡ *̃) R′) │ ((push *̃) S‡) ]
   gamma₁-│•ᵇ {Γ} {x = x} {y} {a = a} {E} {E′} 𝐸 F P Q S† S‡ R′ P′ y† y‡ ≡R′ ≡P′ ≡S† ≡S‡ ≡y† IH =
      let T : Actionᵇ Γ → Set
          T = λ a′ → (ᴿ.pop y *) (ᵀ.tgt E′) —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
          pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸)))
          P″ = tgt (E/E′ (⊖₁ 𝐸)) R′
          α : (ᴿ.pop (ᴺ.suc y) *) (tgt₁ (⊖₁ 𝐸)) ≡ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
          α = let open EqReasoning (setoid _) in
             begin
                (ᴿ.pop (ᴺ.suc y) *) (tgt₁ (⊖₁ 𝐸))
             ≡⟨ cong (ᴿ.pop (ᴺ.suc y) *) (swap-swap (γ₁ 𝐸)) ⟩
                (ᴿ.pop (ᴺ.suc y) *) ((ᴿ.swap *) (tgt₂ (⊖₁ 𝐸)))
             ≡⟨ sym (pop∘swap y _) ⟩
                (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
             ∎
          β : (swap *̃) P′ ≅ P″
          β = let open ≅-Reasoning in
             begin
                (swap *̃) P′
             ≡⟨ cong (swap *̃) (sym ≡P′) ⟩
                (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
             ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) ⟩
                braiding (ᵇ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
             ≡⟨ IH ⟩
                tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
             ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                P″
             ∎
          δ : (pop y† *̃) P′ ≅ tgt pop-y*E/E′ (((pop y‡) *̃) R′)
          δ = let open ≅-Reasoning in
             begin
                (pop y† *̃) P′
             ≅⟨ ≅-cong✴ ↓_ (swap-swap (γ₁ 𝐸)) (pop y† *̃) (swap-swap̃ β) ⟩
                (pop y† *̃) ((swap *̃) P″)
             ≡⟨ cong (λ y → (pop y *̃) ((swap *̃) P″)) ≡y† ⟩
                (pop ((push ᴿ̃.*) y‡) *̃) ((swap *̃) P″)
             ≅⟨ ≅-sym (pop∘swap̃ y‡ P″) ⟩
                (suc (pop y‡) *̃) P″
             ≡⟨ renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (pop y‡) R′ ⟩
                tgt (((ᴿ.pop y) *ᵇ) (E/E′ (⊖₁ 𝐸))) (((pop y‡) *̃) R′)
             ≅⟨ ≅-cong✴ T (pop∘push y a) (λ E† → tgt E† ((pop y‡ *̃) R′))
                        (≅-sym (≡-subst-removable T (pop∘push y a) _)) ⟩
                tgt pop-y*E/E′ (((pop y‡) *̃) R′)
             ∎ in ≅-to-≡ (
      let open ≅-Reasoning in
      begin
         braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ α refl) [ (pop y† *̃) P′ │ S† ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ α refl) _ ⟩
         [ (pop y† *̃) P′ │ S† ]
      ≅⟨ [-│-]-cong α δ refl (≡-to-≅ (trans (sym ≡S†) (trans (sym (renᶜ-tgt-comm F push Q))
                                                             (cong (push *̃) ≡S‡)))) ⟩
         [ tgt pop-y*E/E′ ((pop y‡ *̃) R′) │ (push *̃) S‡ ]
      ∎)
-}
