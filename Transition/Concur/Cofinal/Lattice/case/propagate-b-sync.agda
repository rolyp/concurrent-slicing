open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-b-sync
   {Γ x y P₀ Q₀ R₀ S₀ S′₀} {a : Actionᵇ Γ} {F : Q₀ —[ a ᵇ - _ ]→ S₀} {F′ : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S′₀}
   (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᵇ∇ᶜ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᵇ∇ᶜ {a = a} {• x 〈 y 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   where

   import Name as ᴺ
   import Ren as ᴿ
   import Ren.Lattice as ᴿ̃
   import Transition as ᵀ

   module _
      (R : ↓ R₀) (R† : ↓ (ᴿ.suc ᴿ.push *) R₀) (S′ : ↓ S′₀) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (y† : ↓ ᴺ.suc y) (y‡ : ↓ y)
      (≡R : tgt E P ≡ R) (≡R† : tgt ((ᴿ.push *ᵇ) E) ((push *̃) P) ≡ R†)
      (≡S′ : tgt F′ Q ≡ S′) (≡Q′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ Q′) (y†≡push*y‡ : y† ≡ (push ̃) y‡)

      where
         subcase :
             braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (sym (pop∘suc-push y R₀)) (γ₁ 𝐹))
             [ (pop y† *̃) R† │ Q′ ] ≡
             [ (push *̃) ((pop y‡ *̃) R) │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
         subcase =
            let α : (pop y† *̃) R† ≅ (push *̃) ((pop y‡ *̃) R)
                α = let open ≅-Reasoning in
                   begin
                      (pop y† *̃) R†
                   ≡⟨ cong (pop y† *̃) (sym ≡R†) ⟩
                      (pop y† *̃) (tgt ((ᴿ.push *ᵇ) E) ((push *̃) P))
                   ≡⟨ cong ((pop y† *̃)) (sym (renᵇ-tgt-comm E push P)) ⟩
                      (pop y† *̃) ((suc push *̃) (tgt E P))
                   ≡⟨ cong (λ y → (pop y *̃) ((suc push *̃) (tgt E P))) y†≡push*y‡ ⟩
                      (pop ((push ̃) y‡) *̃) ((suc push *̃) (tgt E P))
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
               braiding ᵇ∇ᶜ (cong₂ _│_ (sym (pop∘suc-push y R₀)) (γ₁ 𝐹)) [ (pop y† *̃) R† │ Q′ ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ (sym (pop∘suc-push y R₀)) (γ₁ 𝐹)) _ ⟩
               [ (pop y† *̃) R† │ Q′ ]
            ≅⟨ [-│-]-cong (sym (pop∘suc-push y R₀)) α (γ₁ 𝐹) β ⟩
               [ (push *̃) ((pop y‡ *̃) R) │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
            ∎)

   case :
      braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (sym (pop∘suc-push y R₀)) (γ₁ 𝐹))
      (tgt ((ᴿ.push *ᵇ) E │• E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F) [ P │ Q ]))
      ≡
      tgt ((ᴿ.pop y *) R₀ │ᵇ E/E′ (⊖₁ 𝐹)) (tgt (E │• F′) [ P │ Q ])
   case
      with step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) | step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q) | inspect (step E) P |
           inspect (step ((ᴿ.push *ᵇ) E)) ((push *̃) P)
   ... | ◻ , S′ | ◻ , Q′ | ◻ , R | ◻ , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      subcase R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
   ... | _ | _ | [ _ ᵇ ] , R | ◻ , R† | _ | _ | [ ≡R ] | [ ≡R† ] =
      ⊥-elim (◻≢[-] (sym (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R†)))))
   ... | _ | _ | ◻ , R | [ _ ᵇ ] , R† | _ | _ | [ ≡R ] | [ ≡R† ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R†))))
   ... | ◻ , S′ | ◻ , Q′ | [ (._ •) ᵇ ] , R | [ (.(ᴺ.suc x) •) ᵇ ] , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      subcase R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
   ... | ◻ , S′ | [ • ._ 〈 _ 〉 ᶜ ] , Q′ | _ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ | _ =
      ⊥-elim (◻≢[-] (trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′))))
   ... | [ • ._ 〈 _ 〉 ᶜ ] , S′ | ◻ , _ | _ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ | _ =
      ⊥-elim (◻≢[-] (sym (trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′)))))
   ... | [ • .x 〈 y‡ 〉 ᶜ ] , S′ | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , Q′ | ◻ , R | ◻ , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      let α : [ • ᴺ.suc x 〈 (push ̃) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′)) in
      subcase R R† S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α))
   ... | [ • .x 〈 y‡ 〉 ᶜ ] , S′ | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , Q′ | [ (.x •) ᵇ ] , R | [ .(ᴺ.suc x) • ᵇ ] , R†
       | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      let α : [ • ᴺ.suc x 〈 (push ̃) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′)) in
      subcase R R† S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α))
