open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.Helpers.propagate-c-sync
   {Γ x y P₀ Q₀ R₀ S₀ S′₀} {a : Actionᶜ Γ} {F : Q₀ —[ a ᶜ - _ ]→ S₀} {F′ : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S′₀}
   (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᶜ∇ᶜ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᶜ∇ᶜ {a = a} {• x 〈 y 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   where

   import Ren as ᴿ
   import Transition as ᵀ

   module _
      (R : ↓ R₀) (S′ : ↓ S′₀) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (y† y‡ : ↓ y) (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′)
      (≡Q′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ Q′) (y†≡y‡ : y† ≡ y‡)
      where

      subcase :
         braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ refl (γ₁ 𝐹))
         [ (pop y‡ *̃) R │ Q′ ]
         ≡
         [ (pop y† *̃) R │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
      subcase =
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
         ≅⟨ [-│-]-cong refl (≡-to-≅ (cong (λ y → (pop y *̃) R) (sym y†≡y‡))) (γ₁ 𝐹) α ⟩
            [ (pop y† *̃) R │ tgt (E/E′ (⊖₁ 𝐹)) S′ ]
         ∎)

   case :
      braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ refl (γ₁ 𝐹))
      (tgt (E │• E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F) [ P │ Q ]))
      ≡
      tgt ((ᴿ.pop y *) R₀ │ᶜ E/E′ (⊖₁ 𝐹)) (tgt (E │• F′) [ P │ Q ])
   case
      with step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) | step E P |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q) | inspect (step E) P
   ... | ◻ , S′ | ◻ , Q′ | ◻ , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      subcase R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
   ... | ◻ , S′ | ◻ , Q′ | [ (._ •) ᵇ ] , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      subcase R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
   ... | ◻ , S′ | [ _ ] , Q′ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′))))
   ... | [ _ ] , S′ | ◻ , Q′ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′)))))
   ... | [ _ ᶜ ] , S′ | [ _ ᶜ ] , Q′ | ◻ , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      subcase R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
   ... | [ • ._ 〈 y† 〉 ᶜ ] , S′ | [ • .x 〈 y‡ 〉 ᶜ ] , Q′ | [ (.x •) ᵇ ] , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      let α : [ • x 〈 y‡ 〉 ᶜ ] ≡ [ • x 〈 y† 〉 ᶜ ]
          α = trans (sym (,-inj₁ ≡Q′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡S′)) in
      subcase R S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α))
