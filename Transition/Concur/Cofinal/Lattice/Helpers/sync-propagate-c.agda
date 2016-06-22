open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.Helpers.sync-propagate-c
   {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᶜ Γ} {E : P₀ —[ a ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
   (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᶜ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (let T : Actionᶜ Γ → Set
        T a′ = (ᴿ.pop y *) R′₀ —[ a′ ᶜ - _ ]→ (ᴿ.pop y *) (tgt₂ (⊖₁ 𝐸))
        pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᶜ) (E/E′ (⊖₁ 𝐸))))
   where

   module _
      (S† : ↓ tgt₁ (⊖₁ 𝐸)) (S‡ : ↓ S₀) (R′ : ↓ R′₀) (y‡ : ↓ y) (≡R′ : tgt E′ P ≡ R′)
      (≡S† : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ S†) (≡S‡ : tgt F Q ≡ S‡)
      where

      subcase :
         braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (cong (ᴿ.pop y *) (γ₁ 𝐸)) refl)
         [ (pop y‡ *̃) S† │ S‡ ]
         ≡
         [ tgt pop-y*E/E′ ((pop y‡ *̃) R′) │ S‡ ]
      subcase =
         let β : S† ≅ tgt (E/E′ (⊖₁ 𝐸)) R′
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

   case :
      braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (cong (ᴿ.pop y *) (γ₁ 𝐸)) refl)
      (tgt (E′/E (⊖₁ 𝐸) │• F) (tgt (E ᶜ│ Q₀) [ P │ Q ]))
      ≡
      tgt (pop-y*E/E′ ᶜ│ S₀) (tgt (E′ │• F) [ P │ Q ])
   case
      with step E′ P | step (E′/E (⊖₁ 𝐸)) (tgt E P) | step F Q |
           inspect (step E′) P | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step F) Q
   ... | ◻ , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      subcase S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡)
   ... | ◻ , R′ | [ (.x •) ᵇ ] , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡S†))))
   ... | [ (.x •) ᵇ ] , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡S†)))))
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      subcase S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡)
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      subcase S† S‡ R′ y‡ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡)
