open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.Helpers.sync-propagate-c
   {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᶜ Γ} {E : P₀ —[ a ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
   (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᶜ∇ᵇ {a = a} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   where

   import Ren as ᴿ

   case :
      braiding (ᶜ∇ᶜ {a = a} {τ}) {0} (cong₂ _│_ (cong (ᴿ.pop y *) (γ₁ 𝐸)) refl)
      (tgt (E′/E (⊖₁ 𝐸) │• F) (tgt (E ᶜ│ Q₀) [ P │ Q ]))
      ≡
      tgt (subst (λ a → (ᴿ.pop y *) R′₀ —[ a ᶜ - _ ]→ (ᴿ.pop y *) (tgt₂ (⊖₁ 𝐸)))
                 (pop∘push y a) ((ᴿ.pop y *ᶜ) (E/E′ (⊖₁ 𝐸))) ᶜ│ S₀)
          (tgt (E′ │• F) [ P │ Q ])
   case
      with step E′ P | step (E′/E (⊖₁ 𝐸)) (tgt E P) | step F Q |
           inspect (step E′) P | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step F) Q
   ... | ◻ , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      {!!} -- gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ (.x •) ᵇ ] , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡S†))))
   ... | [ (.x •) ᵇ ] , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡S†)))))
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      {!!} -- gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      {!!} -- gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ y‡ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
