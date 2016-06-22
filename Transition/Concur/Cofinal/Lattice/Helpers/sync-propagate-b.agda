open import ConcurrentSlicingCommon
import Relation.Binary.EqReasoning as EqReasoning

open import Transition.Concur.Cofinal.Lattice.Common
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.Helpers.sync-propagate-b
   {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᵇ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
   (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᵇ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (let α = let open EqReasoning (setoid _) in
           begin
              (ᴿ.pop (ᴿ.push y) *) (tgt₁ (⊖₁ 𝐸))
           ≡⟨ cong (ᴿ.pop (ᴿ.push y) *) (swap-swap (γ₁ 𝐸)) ⟩
              (ᴿ.pop (ᴿ.push y) *) ((ᴿ.swap *) (tgt₂(⊖₁ 𝐸)))
           ≡⟨ sym (pop∘swap y _) ⟩
              (ᴿ.suc (ᴿ.pop y) *) (tgt₂(⊖₁ 𝐸))
           ∎
        T : Actionᵇ Γ → Set
        T a′ = (ᴿ.pop y *) R′₀ —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
        pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))))
      where

   import Name as ᴺ
   import Ren.Lattice as ᴿ̃

   module _
      (S† : ↓ (ᴿ.push *) S₀) (S‡ : ↓ S₀) (R′ : ↓ R′₀) (P′ : ↓ tgt₁ (⊖₁ 𝐸)) (y† : ↓ ᴺ.suc y) (y‡ : ↓ y)
      (≡R′ : tgt E′ P ≡ R′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′)
      (≡S† : tgt ((ᴿ.push *ᶜ) F) ((push *̃) Q) ≡ S†) (≡S‡ : tgt F Q ≡ S‡) (y†≡push*y‡ : y† ≡ (push ᴿ̃.*) y‡)
      where

      subcase :
         braiding (ᵇ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ α refl)
         [ (pop y† *̃) P′ │ S† ]
         ≡
         [ tgt pop-y*E/E′ ((pop y‡ *̃) R′) │ ((push *̃) S‡) ]
      subcase =
         let P″ = tgt (E/E′ (⊖₁ 𝐸)) R′
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
                ≡⟨ cong (λ y → (pop y *̃) ((swap *̃) P″)) y†≡push*y‡ ⟩
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

   case :
      braiding (ᵇ∇ᶜ {a = a} {τ}) {0}
      (cong₂ _│_ α refl)
      (tgt (E′/E (⊖₁ 𝐸) │• (ᴿ.push *ᶜ) F) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
      ≡
      tgt (subst (λ a′ → (ᴿ.pop y *) R′₀ —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸)))
                 (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) ᵇ│ S₀)
      (tgt (E′ │• F) [ P │ Q ])
   case
      with step E′ P | inspect (step E′) P
   case | ◻ , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (tgt E P) | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
   ... | ◻ , P′ | [ ≡P′ ] =
      let S† = tgt ((ᴿ.push *ᶜ) F) ((push *̃) Q); S‡ = tgt F Q in
      subcase S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) refl refl refl
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
   case
      | [ ._ • ᵇ ] , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (tgt E P) | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) |
           step F Q | inspect (step F) Q
   ... | ◻ , P′ | [ ≡P′ ] | ◻ , S‡ | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] | ◻ , S‡ | [ ≡S‡ ]
      with step ((ᴿ.push *ᶜ) F) ((push *̃) Q) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | [ ≡S† ] =
      subcase S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) refl
   ... | [ • ._ 〈 y′ 〉 ᶜ ] , S† | [ ≡S† ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†))))
   case
      | [ ._ • ᵇ ] , R′ | [ ≡R′ ] | ◻ , P′ | [ ≡P′ ] | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   case
      | [ ._ • ᵇ ] , R′ | [ ≡R′ ] | [ ._ • ᵇ ] , P′ | [ ≡P′ ] | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡S‡ ]
      with step ((ᴿ.push *ᶜ) F) ((push *̃) Q) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | [ ≡S† ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S†)) (trans (sym (renᶜ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S‡)))))
   ... | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , S† | [ ≡S† ] =
      let α : [ • ᴺ.suc x 〈 (push ᴿ̃.*) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†)) in
      subcase S† S‡ R′ P′ y† y‡ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (sym ([•x〈-〉ᶜ]-inj α))
