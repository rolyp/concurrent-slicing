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
