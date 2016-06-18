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

   gamma₁-│•ᶜ : ∀ {Γ x y P₀ R₀ R′₀ Q₀ S₀} {a : Actionᶜ Γ} {E : P₀ —[ a ᶜ - _ ]→ R₀} {E′ : P₀ —[ (x •) ᵇ - _ ]→ R′₀}
                (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀) (S† : ↓ tgt₁ (⊖₁ 𝐸))
                (S‡ : ↓ S₀) (R′ : ↓ R′₀) (y‡ : ↓ y) →
                tgt E′ P ≡ R′ → tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ S† → tgt F Q ≡ S‡ →
                braiding (ᶜ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
                tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
                let T : Actionᶜ Γ → Set
                    T = (λ a → (ᴿ.pop y *) (ᵀ.tgt E′) —[ a ᶜ - _ ]→ (ᴿ.pop y *) (tgt₂ (⊖₁ 𝐸)))
                    pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᶜ) (E/E′ (⊖₁ 𝐸))) in
                braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (cong (ᴿ.pop y *) (γ₁ 𝐸)) refl)
                [ (pop y‡ *̃) S† │ S‡ ] ≡
                [ tgt pop-y*E/E′ ((pop y‡ *̃) R′) │ S‡ ]
   gamma₁-│•ᶜ {Γ} {x = x} {y} {a = a} {E} {E′} 𝐸 F P Q S† S‡ R′ y‡ ≡R′ ≡S† ≡S‡ IH =
      let T : Actionᶜ Γ → Set
          T = (λ a → (ᴿ.pop y *) (ᵀ.tgt E′) —[ a ᶜ - _ ]→ (ᴿ.pop y *) (tgt₂ (⊖₁ 𝐸)))
          pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᶜ) (E/E′ (⊖₁ 𝐸)))
          β : S† ≅ tgt (E/E′ (⊖₁ 𝐸)) R′
          β = let open ≅-Reasoning in
             begin
                S†
             ≡⟨ sym ≡S† ⟩
                tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
             ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _) ⟩
                braiding (ᶜ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
             ≡⟨ IH ⟩
                tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
             ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                tgt (E/E′ (⊖₁ 𝐸)) R′
             ∎
          δ : (pop y‡ *̃) S† ≅ tgt pop-y*E/E′ ((pop y‡ *̃) R′)
          δ = let open ≅-Reasoning in
             begin
                (pop y‡ *̃) S†
             ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) (pop y‡ *̃) β ⟩
                (pop y‡ *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′)
             ≡⟨ renᶜ-tgt-comm (E/E′ (⊖₁ 𝐸)) (pop y‡) R′ ⟩
                tgt (((ᴿ.pop y) *ᶜ) (E/E′ (⊖₁ 𝐸))) ((pop y‡ *̃) R′)
             ≅⟨ ≅-cong✴ T (pop∘push y a) (λ E† → tgt E† ((pop y‡ *̃) R′))
                        (≅-sym (≡-subst-removable T (pop∘push y a) _)) ⟩
                tgt pop-y*E/E′ ((pop y‡ *̃) R′)
             ∎
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (cong (ᴿ.pop y *) (γ₁ 𝐸)) refl) [ (pop y‡ *̃) S† │ S‡ ]
      ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ (cong (ᴿ.pop y *) (γ₁ 𝐸)) refl) _ ⟩
         [ (pop y‡ *̃) S† │ S‡ ]
      ≅⟨ [-│]-cong S‡ (cong (ᴿ.pop y *) (γ₁ 𝐸)) δ ⟩
         [ tgt pop-y*E/E′ ((pop y‡ *̃) R′) │ S‡ ]
      ∎)

   gamma₁-ᵇ│• : ∀ {Γ x y P₀ Q₀ R₀ S₀ S′₀} {a : Actionᵇ Γ} (E : P₀ —[ x • ᵇ - _ ]→ R₀) {F : Q₀ —[ a ᵇ - _ ]→ S₀}
                {F′ : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S′₀} (𝐹 : F ⌣₁[ ᵇ∇ᶜ ] F′) (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀)
                (R† : ↓ (ᴿ.suc ᴿ.push *) R₀) (S′ : ↓ S′₀) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (y† : ↓ ᴺ.suc y) (y‡ : ↓ y) →
                tgt E P ≡ R → tgt ((ᴿ.push *ᵇ) E) ((push *̃) P) ≡ R† → tgt F′ Q ≡ S′ → tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ Q′ →
                y† ≡ (push ᴿ̃.*) y‡ →
                braiding (ᵇ∇ᶜ {a = a} {• x 〈 y 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡
                tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q) →
                braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (sym (pop∘suc-push y R₀)) (γ₁ 𝐹))
                [ (pop y† *̃) R† │ Q′ ] ≡
                [ (push *̃) ((pop y‡ *̃) R) │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
   gamma₁-ᵇ│• {x = x} {y} {a = a} E {F} {F′} 𝐹 P Q R R† S′ Q′ y† y‡ ≡R ≡R† ≡S′ ≡Q′ ≡y† IH =
      let α : (pop y† *̃) R† ≅ (push *̃) ((pop y‡ *̃) R)
          α = let open ≅-Reasoning in
             begin
                (pop y† *̃) R†
             ≡⟨ cong (pop y† *̃) (sym ≡R†) ⟩
                (pop y† *̃) (tgt ((ᴿ.push *ᵇ) E) ((push *̃) P))
             ≡⟨ cong ((pop y† *̃)) (sym (renᵇ-tgt-comm E push P)) ⟩
                (pop y† *̃) ((suc push *̃) (tgt E P))
             ≡⟨ cong (λ y → (pop y *̃) ((suc push *̃) (tgt E P))) ≡y† ⟩
                (pop ((push ᴿ̃.*) y‡) *̃) ((suc push *̃) (tgt E P))
             ≅⟨ ≅-sym (pop∘suc-push̃ y‡ (tgt E P)) ⟩
                (push *̃) ((pop y‡ *̃) (tgt E P))
             ≡⟨ cong ((push *̃) ∘ᶠ (pop y‡ *̃)) ≡R ⟩
                (push *̃) ((pop y‡ *̃) R)
             ∎
          β : Q′ ≅ tgt (E/E′ (⊖₁ 𝐹)) S′
          β = let open ≅-Reasoning in
             begin
                Q′
             ≡⟨ sym ≡Q′ ⟩
                tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
             ≅⟨ ≅-sym (reduce-ᵇ∇ᶜ {a = a} {• x 〈 y 〉} (γ₁ 𝐹) _) ⟩
                braiding ᵇ∇ᶜ {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
             ≡⟨ IH ⟩
                tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
             ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                tgt (E/E′ (⊖₁ 𝐹)) S′
             ∎
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᶜ (cong₂ _│_ (sym (pop∘suc-push y (ᵀ.tgt E))) (γ₁ 𝐹)) [ (pop y† *̃) R† │ Q′ ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ (sym (pop∘suc-push y (ᵀ.tgt E))) (γ₁ 𝐹)) _ ⟩
         [ (pop y† *̃) R† │ Q′ ]
      ≅⟨ [-│-]-cong (sym (pop∘suc-push y (ᵀ.tgt E))) α (γ₁ 𝐹) β ⟩
         [ (push *̃) ((pop y‡ *̃) R) │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
      ∎)

   gamma₁-ᶜ│• : ∀ {Γ x y P₀ Q₀ R₀ S₀ S′₀} {a : Actionᶜ Γ} (E : P₀ —[ x • ᵇ - _ ]→ R₀) {F : Q₀ —[ a ᶜ - _ ]→ S₀}
                {F′ : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S′₀} (𝐹 : F ⌣₁[ ᶜ∇ᶜ ] F′) (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀)
                (S′ : ↓ S′₀) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (y† y‡ : ↓ y) → tgt E P ≡ R → tgt F′ Q ≡ S′ →
                tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ Q′ → y† ≡ y‡ →
                braiding (ᶜ∇ᶜ {a = a} {• x 〈 y 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡
                tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q) →
                braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ refl (γ₁ 𝐹))
                [ (pop y‡ *̃) R │ Q′ ] ≡
                [ (pop y† *̃) R │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
   gamma₁-ᶜ│• {x = x} {y} {a = a} E {F} {F′} 𝐹 P Q R S′ Q′ y† y‡ ≡R ≡S′ ≡Q′ ≡y† IH =
      let α : Q′ ≅ tgt (E/E′ (⊖₁ 𝐹)) S′
          α = let open ≅-Reasoning in
             begin
                Q′
             ≡⟨ sym ≡Q′ ⟩
                tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
             ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐹) _) ⟩
                braiding (ᶜ∇ᶜ {a = a} {• x 〈 y 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
             ≡⟨ IH ⟩
                tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
             ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                tgt (E/E′ (⊖₁ 𝐹)) S′
             ∎
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ (pop y‡ *̃) R │ Q′ ]
      ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ (pop y‡ *̃) R │ Q′ ]
      ≅⟨ [-│-]-cong refl (≡-to-≅ (cong (λ y → (pop y *̃) R) (sym ≡y†))) (γ₁ 𝐹) α ⟩
         [ (pop y† *̃) R │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
      ∎)

   module │ᵥᵇ-x•
      {Γ} {x x′ : Name Γ} {P₀ R₀ R′₀ S₀ Q₀} {E : P₀ —[ x′ • ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸)) (P : ↓ P₀) (Q : ↓ Q₀) (P′ : ↓ P′₀) (S′ : ↓ (ᴿ.suc ᴿ.push *) S₀)
      (id*E/E′ : (idᶠ *) R′₀ —[ ᴺ.suc x′ • ᵇ - _ ]→ (ᴿ.suc idᶠ *) P″₀) (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero)
      (≡id*E/E′ : (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
      (≡S′ : tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ≡ S′) (≡R′ : tgt E′ P ≡ R′)
      (let α : (idᶠ *) P′₀ ≡ (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
           α = (let open EqReasoning (setoid _) in
             begin
                (idᶠ *) P′₀
             ≡⟨ *-preserves-id P′₀ ⟩
                P′₀
             ≡⟨ swap-swap (γ₁ 𝐸) ⟩
                (ᴿ.swap *) P″₀
             ≡⟨ cong (ᴿ.swap *) (sym (+-id-elim 1 P″₀)) ⟩
                (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
             ∎))
      (IH : braiding (ᵇ∇ᵇ {a = x′ •} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      subcase :
         (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
         braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
         [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
         [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
      subcase P″ ≡P″ = ≅-to-≡ (
         let β = (repl ((weaken ᴿ̃.*) y) *̃) P′ ≅ (swap *̃) P″
             β = let open ≅-Reasoning in
                begin
                   (repl ((weaken ᴿ̃.*) y) *̃) P′
                ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym ≡P′) ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-cong✴ ↓_ (sym ((swap-involutive P′₀)))
                           (repl ((weaken ᴿ̃.*) y) *̃) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃)
                   ((swap *̃) (braiding (ᵇ∇ᵇ {a = x′ •} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) IH ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≅⟨ id-swap-id̃ y (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) ⟩
                   (swap *̃) ((suc (repl y) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≡⟨ cong (swap *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P)) ⟩
                   (swap *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P)))
                ≡⟨ cong (λ E† → (swap *̃) (tgt E† ((repl y *̃) (tgt E′ P)))) ≡id*E/E′ ⟩
                   (swap *̃) (tgt id*E/E′ ((repl y *̃) (tgt E′ P)))
                ≡⟨ cong ((swap *̃) ∘ᶠ tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′ ⟩
                   (swap *̃) (tgt id*E/E′ ((repl y *̃) R′))
                ≡⟨ cong (swap *̃) ≡P″ ⟩
                   (swap *̃) P″
                ∎
             δ : S′ ≅ (swap *̃) ((push *̃) S)
             δ = let open ≅-Reasoning in
                begin
                   S′
                ≡⟨ sym ≡S′ ⟩
                   tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q)
                ≡⟨ sym (renᵇ-tgt-comm F push Q) ⟩
                   (suc push *̃) (tgt F Q)
                ≅⟨ swap∘push̃ _ ⟩
                   (swap *̃) ((push *̃) (tgt F Q))
                ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃)) ≡S ⟩
                   (swap *̃) ((push *̃) S)
                ∎
             open ≅-Reasoning in
         begin
            braiding ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
         ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀))) _ ⟩
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
         ≅⟨ [ν-]-cong (cong₂ _│_ α (swap∘push S₀)) ([-│-]-cong α β (swap∘push S₀) δ) ⟩
            [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
         ∎)

      case :
         braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
         [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
         π₂ (step⁻ (νᵇ (id*E/E′ ᵇ│ S₀)) (ν [ (repl y *̃) R′ │ S ]))
      case
         with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
      ... | ◻ , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)
      ... | [ ._ • ᵇ ] , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)

   module │ᵥᵇ-•x
      {Γ} {x x′ : Name Γ} {P₀ R₀ R′₀ S₀ Q₀} {E : P₀ —[ (• x′) ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸)) (P : ↓ P₀) (Q : ↓ Q₀) (P′ : ↓ P′₀) (S′ : ↓ (ᴿ.suc ᴿ.push *) S₀)
      (id*E/E′ : (idᶠ *) R′₀ —[ (• ᴺ.suc x′) ᵇ - _ ]→ (ᴿ.suc idᶠ *) P″₀) (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero)
      (≡id*E/E′ : (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
      (≡S′ : tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ≡ S′) (≡R′ : tgt E′ P ≡ R′)
      (let α : (idᶠ *) P′₀ ≡ (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
           α = (let open EqReasoning (setoid _) in
             begin
                (idᶠ *) P′₀
             ≡⟨ *-preserves-id P′₀ ⟩
                P′₀
             ≡⟨ swap-swap (γ₁ 𝐸) ⟩
                (ᴿ.swap *) P″₀
             ≡⟨ cong (ᴿ.swap *) (sym (+-id-elim 1 P″₀)) ⟩
                (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
             ∎))
      (IH : braiding (ᵇ∇ᵇ {a = • x′} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      subcase :
         (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
         [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
         [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
      subcase P″ ≡P″ = ≅-to-≡ (
         let β = (repl ((weaken ᴿ̃.*) y) *̃) P′ ≅ (swap *̃) P″
             β = let open ≅-Reasoning in
                begin
                   (repl ((weaken ᴿ̃.*) y) *̃) P′
                ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym ≡P′) ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-cong✴ ↓_ (sym ((swap-involutive P′₀)))
                           (repl ((weaken ᴿ̃.*) y) *̃) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃)
                   ((swap *̃) (braiding (ᵇ∇ᵇ {a = • x′} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) IH ⟩
                   (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≅⟨ id-swap-id̃ y (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) ⟩
                   (swap *̃) ((suc (repl y) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≡⟨ cong (swap *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P)) ⟩
                   (swap *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P)))
                ≡⟨ cong (λ E† → (swap *̃) (tgt E† ((repl y *̃) (tgt E′ P)))) ≡id*E/E′ ⟩
                   (swap *̃) (tgt id*E/E′ ((repl y *̃) (tgt E′ P)))
                ≡⟨ cong ((swap *̃) ∘ᶠ tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′ ⟩
                   (swap *̃) (tgt id*E/E′ ((repl y *̃) R′))
                ≡⟨ cong (swap *̃) ≡P″ ⟩
                   (swap *̃) P″
                ∎
             δ : S′ ≅ (swap *̃) ((push *̃) S)
             δ = let open ≅-Reasoning in
                begin
                   S′
                ≡⟨ sym ≡S′ ⟩
                   tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q)
                ≡⟨ sym (renᵇ-tgt-comm F push Q) ⟩
                   (suc push *̃) (tgt F Q)
                ≅⟨ swap∘push̃ _ ⟩
                   (swap *̃) ((push *̃) (tgt F Q))
                ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃)) ≡S ⟩
                   (swap *̃) ((push *̃) S)
                ∎
             open ≅-Reasoning in
         begin
            braiding ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
         ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀))) _ ⟩
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
         ≅⟨ [ν-]-cong (cong₂ _│_ α (swap∘push S₀)) ([-│-]-cong α β (swap∘push S₀) δ) ⟩
            [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
         ∎)

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
         [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
         π₂ (step⁻ (νᵇ (id*E/E′ ᵇ│ S₀)) (ν [ (repl y *̃) R′ │ S ]))
      case
         with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
      ... | ◻ , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)
      ... | [ (• ._) ᵇ ] , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)

   module │ᵥᶜ-τ
      {Γ} {x : Name Γ} {P₀ R₀ R′₀ S₀ Q₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸)) (P : ↓ P₀) (Q : ↓ Q₀) (P′ : ↓ P′₀)
      (id*E/E′ : (idᶠ *) R′₀ —[ τ ᶜ - _ ]→ (idᶠ *) P″₀) (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero)
      (≡id*E/E′ : (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
      (≡R′ : tgt E′ P ≡ R′)
      (IH : braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      subcase :
         (P″ : ↓ (idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
         [ ν [ (repl y *̃) P′ │ S ] ] ≡
         [ ν [ P″ │ S ] ]
      subcase P″ ≡P″ = ≅-to-≡ (
         let α : (repl y *̃) P′ ≅ P″
             α = let open ≅-Reasoning in
                begin
                   (repl y *̃) P′
                ≡⟨ cong (repl y *̃) (sym ≡P′) ⟩
                   (repl y *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl y *̃)) (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (repl y *̃) (braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                ≡⟨ cong (repl y *̃) IH ⟩
                   (repl y *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
                ≡⟨ renᶜ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P) ⟩
                   tgt ((idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P))
                ≡⟨ cong (λ E† → tgt E† ((repl y *̃) (tgt E′ P))) ≡id*E/E′ ⟩
                   tgt id*E/E′ ((repl y *̃) (tgt E′ P))
                ≡⟨ cong (tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′  ⟩
                   tgt id*E/E′ ((repl y *̃) R′)
                ≡⟨ ≡P″ ⟩
                   P″
                ∎
             open ≅-Reasoning in
         begin
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
            [ ν [ (repl y *̃) P′ │ S ] ]
         ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl)) _ ⟩
            [ ν [ (repl y *̃) P′ │ S ] ]
         ≅⟨ [ν-]-cong (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl) ([-│]-cong S (cong (idᶠ *) (γ₁ 𝐸)) α) ⟩
            [ ν [ P″ │ S ] ]
         ∎)

      case :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0}
         (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
         [ ν [ (ᴿ̃.repl y *̃) P′ │ S ] ] ≡
         π₂ (step⁻ (νᶜ (id*E/E′ ᶜ│ S₀)) (ν [ (ᴿ̃.repl y *̃) R′ │ S ]))
      case
         with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
      ... | ◻ , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)
      ... | [ τ ᶜ ] , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)

   module │ᵥᶜ-•x〈y〉
      {Γ} {x x′ y′ : Name Γ} {P₀ R₀ R′₀ S₀ Q₀} {E : P₀ —[ • x′ 〈 y′ 〉 ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸)) (P : ↓ P₀) (Q : ↓ Q₀) (P′ : ↓ P′₀)
      (id*E/E′ : (idᶠ *) R′₀ —[ • ᴺ.suc x′ 〈 ᴺ.suc y′ 〉 ᶜ - _ ]→ (idᶠ *) P″₀) (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero)
      (≡id*E/E′ : (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
      (≡R′ : tgt E′ P ≡ R′)
      (IH : braiding (ᶜ∇ᵇ {a = • x′ 〈 y′ 〉} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      subcase :
         (P″ : ↓ (idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
         braiding (ᶜ∇ᶜ {a = • x′ 〈 y′ 〉} {τ}) {0} (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
         [ ν [ (repl y *̃) P′ │ S ] ] ≡
         [ ν [ P″ │ S ] ]
      subcase P″ ≡P″ = ≅-to-≡ (
         let α : (repl y *̃) P′ ≅ P″
             α = let open ≅-Reasoning in
                begin
                   (repl y *̃) P′
                ≡⟨ cong (repl y *̃) (sym ≡P′) ⟩
                   (repl y *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl y *̃)) (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (repl y *̃) (braiding (ᶜ∇ᵇ {a = • x′ 〈 y′ 〉} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                ≡⟨ cong (repl y *̃) IH ⟩
                   (repl y *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
                ≡⟨ renᶜ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P) ⟩
                   tgt ((idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P))
                ≡⟨ cong (λ E† → tgt E† ((repl y *̃) (tgt E′ P))) ≡id*E/E′ ⟩
                   tgt id*E/E′ ((repl y *̃) (tgt E′ P))
                ≡⟨ cong (tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′  ⟩
                   tgt id*E/E′ ((repl y *̃) R′)
                ≡⟨ ≡P″ ⟩
                   P″
                ∎
             open ≅-Reasoning in
         begin
            braiding (ᶜ∇ᶜ {a = • x′ 〈 y′ 〉} {τ}) {0} (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
            [ ν [ (repl y *̃) P′ │ S ] ]
         ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl)) _ ⟩
            [ ν [ (repl y *̃) P′ │ S ] ]
         ≅⟨ [ν-]-cong (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl) ([-│]-cong S (cong (idᶠ *) (γ₁ 𝐸)) α) ⟩
            [ ν [ P″ │ S ] ]
         ∎)

      case :
         braiding (ᶜ∇ᶜ {a = • x′ 〈 y′ 〉} {τ}) {0}
         (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
         [ ν [ (ᴿ̃.repl y *̃) P′ │ S ] ] ≡
         π₂ (step⁻ (νᶜ (id*E/E′ ᶜ│ S₀)) (ν [ (ᴿ̃.repl y *̃) R′ │ S ]))
      case
         with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
      ... | ◻ , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P″ ] = subcase P″ (,-inj₂ ≡P″)
-}

   module ᵇ│ᵥ-ˣ∇ˣ
      {Γ} {x x′ : Name Γ} {P₀ Q₀ R₀ S₀ S′₀} {F : Q₀ —[ (• x′) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ˣ∇ˣ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀) (R′ : ↓ (ᴿ.suc ᴿ.push *) R₀) (S′ : ↓ S′₀) (Q′ : ↓ Q′₀) (y : ↓ (ᴺ.zero {Γ}))
      (≡R : tgt E P ≡ R) (≡R′ : tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P) ≡ R′) (≡S′ : tgt F′ Q ≡ S′)
      (≡Q′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ Q′)
      (IH : (braiding (ˣ∇ˣ {x = x′} {x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)))
      (let α : (ᴿ.pop ᴺ.zero *) ((ᴿ.suc ᴿ.push *) R₀) ≡ (idᶠ *) R₀
           α = trans (pop-zero∘suc-push R₀) (sym (*-preserves-id R₀)))
      where

      private
         subcase :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
            [ (pop y *̃) R′ │ Q′ ] ≡
            [ (repl y *̃) R │ Q″ ]
         subcase Q″ ≡Q″ =
            let β : (pop y *̃) R′ ≅ (repl y *̃) R
                β = let open ≅-Reasoning in
                   begin
                      (pop y *̃) R′
                   ≡⟨ cong (pop y *̃) (sym ≡R′) ⟩
                      (pop y *̃) (tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P))
                   ≡⟨ cong (pop y *̃) (sym (renᵇ-tgt-comm E push P)) ⟩
                      (pop y *̃) ((suc push *̃) (tgt E P))
                   ≅⟨ pop-zero∘suc-push̃ y _ ⟩
                      (repl y *̃) (tgt E P)
                   ≡⟨ cong ((repl y *̃)) ≡R ⟩
                      (repl y *̃) R
                   ∎
                δ : Q′ ≅ Q″
                δ = let open ≅-Reasoning in
                   begin
                      Q′
                   ≡⟨ sym ≡Q′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x′} {x} (γ₁ 𝐹) _) ⟩
                      braiding (ˣ∇ˣ {x = x′} {x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≡⟨ IH ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) S′
                   ≡⟨ ≡Q″ ⟩
                      Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡(
            begin
               braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹)) [ (pop y *̃) R′ │ Q′ ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ α (γ₁ 𝐹)) _ ⟩
               [ (pop y *̃) R′ │ Q′ ]
            ≅⟨ [-│-]-cong α β (γ₁ 𝐹) δ ⟩
               [ (repl y *̃) R │ Q″ ]
            ∎)

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
         [ (pop y *̃) R′ │ Q′ ] ≡
         π₂ (step⁻ (ν• ((idᶠ *) R₀ │ᶜ E/E′ (⊖₁ 𝐹))) (ν [ (ᴿ̃.repl y *̃) R │ S′ ]))
      case
         with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)
      ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)
{-
   module ᵇ│ᵥ-ᵇ∇ᵇ-x•
      {Γ} {x x′ : Name Γ} {P₀ Q₀ : Proc Γ} {R₀ S₀ S′₀ : Proc (Γ + 1)}
      {F : Q₀ —[ x′ • ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀) (S′ : ↓ S′₀) (P″ : ↓ (ᴿ.suc ᴿ.push *) R₀) (P′ : ↓ Q′₀) (y : ↓ (ᴺ.zero {Γ}))
      (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′) (≡P″ : tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P) ≡ P″)
      (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′)
      (IH : braiding (ᵇ∇ᵇ {a = x′ •} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      (let α : (idᶠ *) ((ᴿ.suc ᴿ.push *) R₀) ≡ (ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀))
           α = let open EqReasoning (setoid _) in
             begin
                (idᶠ *) ((ᴿ.suc ᴿ.push *) R₀)
             ≡⟨ *-preserves-id _ ⟩
                (ᴿ.suc ᴿ.push *) R₀
             ≡⟨ cong (ᴿ.suc ᴿ.push *) (sym (*-preserves-id R₀)) ⟩
                (ᴿ.suc ᴿ.push *) ((idᶠ *) R₀)
             ≡⟨ swap∘push _ ⟩
                (ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀))
             ∎
           β : ν ((idᶠ *) ((ᴿ.suc ᴿ.push *) R₀) │ Q′₀) ≡ ᵀ.tgt (νᵇ ((idᶠ *) R₀ │ᵇ E/E′ (⊖₁ 𝐹)))
           β = cong ν_ (cong₂ _│_ α (swap-swap (γ₁ 𝐹)))) where

      private
         subcase :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ] ≡
            [ ν [ (swap *̃) ((push *̃) ((repl y *̃) R)) │ (swap *̃) Q″ ] ]
         subcase Q″ ≡Q″ =
            let γ : (repl ((weaken ᴿ̃.*) y) *̃) P″ ≅ (swap *̃) ((push *̃) ((repl y *̃) R))
                γ = let open ≅-Reasoning in
                   begin
                      (repl ((weaken ᴿ̃.*) y) *̃) P″
                   ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym ≡P″) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) (tgt ((ᴿ.push *ᵇ) E) ((push *̃) P))
                   ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym (renᵇ-tgt-comm E push P)) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) ((suc push *̃) (tgt E P))
                   ≅⟨ id∘suc-push̃ _ ⟩
                      (suc push *̃) ((repl y *̃) (tgt E P))
                   ≅⟨ swap∘push̃ _ ⟩
                      (swap *̃) ((push *̃) ((repl y *̃) (tgt E P)))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃) ∘ᶠ (repl y *̃)) ≡R ⟩
                      (swap *̃) ((push *̃) ((repl y *̃) R))
                   ∎
                δ : P′ ≅ (swap *̃) Q″
                δ = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (swap-involutivẽ _) ⟩
                      (swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐹) (swap *̃) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _)) ⟩
                      (swap *̃) (braiding (ᵇ∇ᵇ {a = x′ •} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≡⟨ cong (swap *̃) IH ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) S′)
                   ≡⟨ cong (swap *̃) ≡Q″ ⟩
                      (swap *̃) Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ β _ ⟩
               [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap-swap (γ₁ 𝐹))) ([-│-]-cong α γ (swap-swap (γ₁ 𝐹)) δ) ⟩
               [ ν [ (swap *̃) ((push *̃) ((repl y *̃) R)) │ (swap *̃) Q″ ] ]
            ∎)

      case :
         braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β
         [ ν [ (ᴿ̃.repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ] ≡
         π₂ (step⁻ (νᵇ ((idᶠ *) R₀ │ᵇ E/E′ (⊖₁ 𝐹))) (ν [ (ᴿ̃.repl y *̃) R │ S′ ]))
      case
         with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)

   module ᵇ│ᵥ-ᵇ∇ᵇ-•x
      {Γ} {x x′ : Name Γ} {P₀ Q₀ : Proc Γ} {R₀ S₀ S′₀ : Proc (Γ + 1)}
      {F : Q₀ —[ (• x′) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀) (S′ : ↓ S′₀) (P″ : ↓ (ᴿ.suc ᴿ.push *) R₀) (P′ : ↓ Q′₀) (y : ↓ (ᴺ.zero {Γ}))
      (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′) (≡P″ : tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P) ≡ P″)
      (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′)
      (IH : braiding (ᵇ∇ᵇ {a = • x′} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      (let α : (idᶠ *) ((ᴿ.suc ᴿ.push *) R₀) ≡ (ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀))
           α = let open EqReasoning (setoid _) in
             begin
                (idᶠ *) ((ᴿ.suc ᴿ.push *) R₀)
             ≡⟨ *-preserves-id _ ⟩
                (ᴿ.suc ᴿ.push *) R₀
             ≡⟨ cong (ᴿ.suc ᴿ.push *) (sym (*-preserves-id R₀)) ⟩
                (ᴿ.suc ᴿ.push *) ((idᶠ *) R₀)
             ≡⟨ swap∘push _ ⟩
                (ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀))
             ∎
           β : ν ((idᶠ *) ((ᴿ.suc ᴿ.push *) R₀) │ Q′₀) ≡ ᵀ.tgt (νᵇ ((idᶠ *) R₀ │ᵇ E/E′ (⊖₁ 𝐹)))
           β = cong ν_ (cong₂ _│_ α (swap-swap (γ₁ 𝐹)))) where

      private
         subcase :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ] ≡
            [ ν [ (swap *̃) ((push *̃) ((repl y *̃) R)) │ (swap *̃) Q″ ] ]
         subcase Q″ ≡Q″ =
            let γ : (repl ((weaken ᴿ̃.*) y) *̃) P″ ≅ (swap *̃) ((push *̃) ((repl y *̃) R))
                γ = let open ≅-Reasoning in
                   begin
                      (repl ((weaken ᴿ̃.*) y) *̃) P″
                   ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym ≡P″) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) (tgt ((ᴿ.push *ᵇ) E) ((push *̃) P))
                   ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym (renᵇ-tgt-comm E push P)) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) ((suc push *̃) (tgt E P))
                   ≅⟨ id∘suc-push̃ _ ⟩
                      (suc push *̃) ((repl y *̃) (tgt E P))
                   ≅⟨ swap∘push̃ _ ⟩
                      (swap *̃) ((push *̃) ((repl y *̃) (tgt E P)))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃) ∘ᶠ (repl y *̃)) ≡R ⟩
                      (swap *̃) ((push *̃) ((repl y *̃) R))
                   ∎
                δ : P′ ≅ (swap *̃) Q″
                δ = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (swap-involutivẽ _) ⟩
                      (swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐹) (swap *̃) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _)) ⟩
                      (swap *̃) (braiding (ᵇ∇ᵇ {a = • x′} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≡⟨ cong (swap *̃) IH ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) S′)
                   ≡⟨ cong (swap *̃) ≡Q″ ⟩
                      (swap *̃) Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ β _ ⟩
               [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap-swap (γ₁ 𝐹))) ([-│-]-cong α γ (swap-swap (γ₁ 𝐹)) δ) ⟩
               [ ν [ (swap *̃) ((push *̃) ((repl y *̃) R)) │ (swap *̃) Q″ ] ]
            ∎)

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β
         [ ν [ (ᴿ̃.repl ((weaken ᴿ̃.*) y) *̃) P″ │ P′ ] ] ≡
         π₂ (step⁻ (νᵇ ((idᶠ *) R₀ │ᵇ E/E′ (⊖₁ 𝐹))) (ν [ (ᴿ̃.repl y *̃) R │ S′ ]))
      case
         with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)
      ... | [ (• ._) ᵇ ] , Q″ | [ ≡Q″ ] = subcase Q″ (,-inj₂ ≡Q″)

   module │ᵥ
      {Γ} {x u : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀}
      {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ˣ∇ˣ ] F′) (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀)
      (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂(⊖₁ 𝐸); Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂(⊖₁ 𝐹))
      (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      (IH₂ : braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      (let γ : (ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P′₀) ≡ (ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P″₀)
           γ = let open EqReasoning (setoid _) in
             begin
                (ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P′₀)
             ≡⟨ cong (ᴿ.pop ᴺ.zero *) (+-id-elim 1 P′₀) ⟩
                (ᴿ.pop ᴺ.zero *) P′₀
             ≡⟨ sym (pop-swap _) ⟩
                (ᴿ.pop ᴺ.zero *) ((ᴿ.swap *) P′₀)
             ≡⟨ cong (ᴿ.pop ᴺ.zero *) (γ₁ 𝐸) ⟩
                (ᴿ.pop ᴺ.zero *) P″₀
             ≡⟨ cong (ᴿ.pop ᴺ.zero *) (sym (+-id-elim 1 P″₀)) ⟩
                (ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P″₀)
             ∎
           α : ν ((ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P′₀) │ Q′₀) ≡ Proc↱ refl (ν ((ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P″₀) │ Q″₀))
           α = cong ν_ (cong₂ _│_ γ (γ₁ 𝐹))) where

      private
         subcase : (P′ : ↓ (ᴿ.suc idᶠ *) P′₀) (Q′ : ↓ Q′₀) (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (Q″ : ↓ Q″₀)
                   (y y′ : ↓ ᴺ.zero) → tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R) ≡ P′ → tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′ →
                   tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′) ≡ P″ → tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″ → (y† y‡ : ↓ ᴺ.zero) →
                   braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
                   [ ν [ (pop y† *̃) P′ │ Q′ ] ] ≡ [ ν [ (pop y‡ *̃) P″ │ Q″ ] ]
         subcase P′ Q′ P″ Q″ y y′ ≡P′ ≡Q′ ≡P″ ≡Q″ y† y‡ =
            let β : (pop y† *̃) P′ ≅ (pop y‡ *̃) P″
                β = let open ≅-Reasoning in
                   begin
                      (pop y† *̃) P′
                   ≡⟨ cong (pop y† *̃) (sym ≡P′) ⟩
                      (pop y† *̃) (tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R))
                   ≡⟨ cong (pop y† *̃) (sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) (repl y) R)) ⟩
                      (pop y† *̃) ((suc (repl y) *̃) (tgt (E′/E (⊖₁ 𝐸)) R))
                   ≡⟨ cong ((pop y† *̃) ∘ᶠ (suc (repl y) *̃) ∘ᶠ tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
                      (pop y† *̃) ((suc (repl y) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                   ≅⟨ {!!} ⟩
                      (pop y′ *̃) ((suc (repl y‡) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                   ≅⟨ ≅-sym (pop-swap̃ y′ y‡ _) ⟩
                      (pop y‡ *̃) ((suc (repl y′) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                      (pop y‡ *̃) ((suc (repl y′) *̃) (braiding ᵇ∇ᵇ {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≡⟨ cong ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃)) IH₁ ⟩
                      (pop y‡ *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                   ≡⟨ cong ((pop y‡ *̃) ∘ᶠ ((suc (repl y′) *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸)))) ≡R′ ⟩
                      (pop y‡ *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′))
                   ≡⟨ cong (pop y‡ *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y′) R′) ⟩
                      (pop y‡ *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′))
                   ≡⟨ cong (pop y‡ *̃) ≡P″ ⟩
                      (pop y‡ *̃) P″
                   ∎
                δ = Q′ ≅ Q″
                δ = let open ≅-Reasoning in
                   begin
                      Q′
                   ≡⟨ sym ≡Q′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) S
                   ≡⟨ cong (tgt (E′/E (⊖₁ 𝐹))) (sym ≡S) ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐹) _) ⟩
                      braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≡⟨ IH₂ ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) S′
                   ≡⟨ ≡Q″ ⟩
                      Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding ᶜ∇ᶜ {0} α [ ν [ (pop y† *̃) P′ │ Q′ ] ]
            ≅⟨ reduce-ᶜ∇ᶜ α _ ⟩
               [ ν [ (pop y† *̃) P′ │ Q′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ γ (γ₁ 𝐹)) ([-│-]-cong γ β (γ₁ 𝐹) δ) ⟩
               [ ν [ (pop y‡ *̃) P″ │ Q″ ] ]
            ∎)

      case : (y y′ : ↓ ᴺ.zero) →
             braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
             (π₂ (step⁻ (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │• E′/E (⊖₁ 𝐹))) (ν [ (repl y *̃) R │ S ]))) ≡
             π₂ (step⁻ (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │• E/E′ (⊖₁ 𝐹))) (ν [ (repl y′ *̃) R′ │ S′ ]))
      case y y′
         with step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R) | step (E′/E (⊖₁ 𝐹)) S |
              step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′) | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)))) ((repl y *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((repl y′ *̃) R′) | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ q ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ y‡
      ... | ◻ , P′ | [ _ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | [ _ ] , Q′ | ◻ , P″ | [ _ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | [ _ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | [ _ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ y‡
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ _ ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ y‡
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† ◻
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | [ _ ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† ◻
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† ◻
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ y y′ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† y‡
-}

{-
   module │ᵥ′
      {Γ} {x u : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀}
      {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (P : ↓ P₀) (Q : ↓ Q₀) (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀)
      (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′)
      (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      (IH₂ : braiding (ᵇ∇ᵇ {a = • x} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)) where

      private
         coerce-braid : (P′ : ↓ tgt₁ (⊖₁ 𝐸)) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) →
                        braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ] ≅
                        braid̂ (νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹))) [ ν [ ν [ P′ │ Q′ ] ] ]
         coerce-braid _ _ rewrite (sym (γ₁ 𝐸)) | (sym (γ₁ 𝐹)) = ≅-refl

         subcase : (P′ : ↓ tgt₁ (⊖₁ 𝐸)) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (P″ : ↓ tgt₂ (⊖₁ 𝐸)) (Q″ : ↓ tgt₂ (⊖₁ 𝐹)) →
                   tgt (E′/E (⊖₁ 𝐸)) R ≡ P′ → tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′ →
                   tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ P″ →  tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″ →
                   braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ] ≡ [ ν [ ν [ P″ │ Q″ ] ] ]
         subcase P′ Q′ P″ Q″ ≡P′ ≡Q′ ≡P″ ≡Q″ =
            let β : (swap *̃) P′ ≅ P″
                β = let open ≅-Reasoning in
                   begin
                      (swap *̃) P′
                   ≡⟨ cong (swap *̃) (trans (sym ≡P′) (cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R))) ⟩
                      (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) ⟩
                      braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≡⟨ IH₁ ⟩
                      tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
                   ≡⟨ trans (cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′) ≡P″ ⟩
                      P″
                   ∎
                γ : (swap *̃) Q′ ≅ Q″
                γ = let open ≅-Reasoning in
                   begin
                      (swap *̃) Q′
                   ≡⟨ cong (swap *̃) (trans (sym ≡Q′) (cong (tgt (E′/E (⊖₁ 𝐹))) (sym ≡S))) ⟩
                      (swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _) ⟩
                      braiding (ᵇ∇ᵇ {a = • x} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≡⟨ IH₂ ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                   ≡⟨ trans (cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′) ≡Q″ ⟩
                      Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ]
            ≅⟨ coerce-braid P′ Q′ ⟩
               braid̂ (νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹))) [ ν [ ν [ P′ │ Q′ ] ] ]
            ≡⟨ refl ⟩
               [ ν [ ν [ (swap *̃) P′ │ (swap *̃) Q′ ] ] ]
            ≅⟨ [ν-]-cong (cong ν_ (cong₂ _│_ (γ₁ 𝐸) (γ₁ 𝐹)))
                         ([ν-]-cong (cong₂ _│_ (γ₁ 𝐸) (γ₁ 𝐹)) ([-│-]-cong (γ₁ 𝐸) β (γ₁ 𝐹) γ)) ⟩
               [ ν [ ν [ P″ │ Q″ ] ] ]
            ∎)

      case : braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) (π₂ (step⁻ (νᶜ (E′/E (⊖₁ 𝐸) │ᵥ E′/E (⊖₁ 𝐹))) (ν [ R │ S ]))) ≡
             π₂ (step⁻ (νᶜ (E/E′ (⊖₁ 𝐸) │ᵥ E/E′ (⊖₁ 𝐹))) (ν [ R′ │ S′ ]))
      case
         with step (E′/E (⊖₁ 𝐸)) R | step (E′/E (⊖₁ 𝐹)) S | step (E/E′ (⊖₁ 𝐸)) R′ | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         subcase P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
-}
