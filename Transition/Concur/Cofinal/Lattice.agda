module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   import Name as ᴺ
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common
   open import Transition.Concur.Cofinal.Lattice.Helpers
   open import Transition.Concur.Cofinal.Lattice.Helpers.All

   private
      coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
                  let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
      coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

   -- γ₁ lifted to the lattice setting. Can't seem to avoid inspect-on-steroids here, ouch.
   gamma₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
            braiding 𝑎 (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P′)) ≡ coerceCxt 𝑎 (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P′))

{-
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᵇ∇ᵇ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᵇ∇ᶜ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᶜ∇ᵇ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᶜ∇ᶜ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᵛ∇ᵛ} 𝐸 ◻ = refl

   gamma₁ {a = a ᵇ} {a′ ᵇ} {E = .E ᵇ│ Q₀} {E′ = P₀ │ᵇ .F} (E ᵇ│ᵇ F) [ P │ Q ] =
      let S† : π₂ (step ((ᴿ.push *ᵇ) E) ((push *̃) P)) ≅ (swap *̃) ((push *̃) (π₂ (step E P)))
          S† = ≅-trans (≡-to-≅ (sym (renᵇ-tgt-comm E push P))) (swap∘push̃ _)
          S‡ : (push *̃) (π₂ (step F Q)) ≅ (swap *̃) (π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q)))
          S‡ = ≅-trans (swap∘suc-push̃ _) (≡-to-≅ (cong (swap *̃) (renᵇ-tgt-comm F push Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (sym (cong₂ _│_ (swap∘push (ᵀ.tgt E)) (swap∘suc-push (ᵀ.tgt F))))
                                        [ (push *̃) (π₂ (step E P)) │ π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q)) ]
      ≅⟨ reduce-ᵇ∇ᵇ (sym (cong₂ _│_ (swap∘push (ᵀ.tgt E)) (swap∘suc-push (ᵀ.tgt F)))) _ ⟩
         [ (swap *̃) ((push *̃) (π₂ (step E P))) │ (swap *̃) (π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q))) ]
      ≅⟨ ≅-sym ([-│-]-cong (swap∘push (ᵀ.tgt E)) S† (swap∘suc-push (ᵀ.tgt F)) S‡) ⟩
         [ π₂ (step ((ᴿ.push *ᵇ) E) ((push *̃) P)) │ (push *̃) (π₂ (step F Q)) ]
      ∎)

   gamma₁ (E ᵇ│ᶜ F) [ P │ Q ] = cong (λ Q′ → [ _ │ Q′ ]) (sym (renᶜ-tgt-comm F push Q))

   gamma₁ (E ᶜ│ᵇ F) [ P │ Q ] = cong (λ P′ → [ P′ │ _ ]) (renᶜ-tgt-comm E push P)

   gamma₁ (E ᶜ│ᶜ F) [ P │ Q ] = refl

   gamma₁ (𝐸 ➕₁ Q) [ P ➕ _ ] = gamma₁ 𝐸 P

   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = _ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ≅⟨ reduce-ˣ∇ˣ {x = x} {u} (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐹) _)) (≡-to-≅ (gamma₁ 𝐹 Q))) ⟩
         [ (push *̃) P │ S† ]
      ∎)

   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = P₀ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᵇ {0} (cong₂ _│_ (swap∘push∘push P₀) (γ₁ 𝐹)) [ (push *̃) ((push *̃) P) │ S‡ ]
      ≅⟨ reduce-ᵇ∇ᵇ (cong₂ _│_ (swap∘push∘push P₀) (γ₁ 𝐹)) _ ⟩
         [ (swap *̃) ((push *̃) ((push *̃) P)) │ (swap *̃) S‡ ]
      ≅⟨ [-│-]-cong (swap∘push∘push P₀) (swap∘push∘push̃ P)
                    (γ₁ 𝐹) (≅-trans (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) S‡)) (≡-to-≅ (gamma₁ 𝐹 Q))) ⟩
         [ (push *̃) ((push *̃) P) │ S† ]
      ∎)

   gamma₁ {E = _ │ᵇ F} {._ │ᶜ F′} (._ │ᵇᶜ 𝐹) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐹) _)) (≡-to-≅ (gamma₁ 𝐹 Q))) ⟩
         [ (push *̃) P │ S† ]
      ∎)

   gamma₁ {E = _ │ᶜ F} {._ │ᶜ F′} (._ │ᶜᶜ 𝐹) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ P │ S‡ ]
      ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐹) _)) (≡-to-≅ (gamma₁ 𝐹 Q))) ⟩
         [ P │ S† ]
      ∎)

   gamma₁ {E = P₀ │ᶜ F} {._ │ᶜ F′} (._ │ᵛᵛ 𝐹) [ P │ Q ] = cong (λ Q → [ P │ Q ]) (gamma₁ 𝐹 Q)

   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ≅⟨ reduce-ˣ∇ˣ {x = x} {u} (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _)) (≡-to-≅ (gamma₁ 𝐸 P))) ⟩
         [ S† │ (push *̃) Q ]
      ∎)

   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᵇ {0} (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀)) [ S‡ │ (push *̃) ((push *̃) Q) ]
      ≅⟨ reduce-ᵇ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀)) _ ⟩
         [ (swap *̃) S‡ │ (swap *̃) ((push *̃) ((push *̃) Q)) ]
      ≅⟨ [-│-]-cong (γ₁ 𝐸) (≅-trans (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) S‡)) (≡-to-≅ (gamma₁ 𝐸 P)))
                    (swap∘push∘push Q₀) (swap∘push∘push̃ Q) ⟩
         [ S† │ (push *̃) ((push *̃) Q) ]
      ∎)

   gamma₁ {E = E ᵇ│ _} {E′ ᶜ│ ._} (𝐸 ᵇᶜ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _)) (≡-to-≅ (gamma₁ 𝐸 P))) ⟩
         [ S† │ (push *̃) Q ]
      ∎)

   gamma₁ {E = E ᶜ│ _} {E′ ᶜ│ ._} (𝐸 ᶜᶜ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │  Q ]
      ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
         [ S‡ │ Q ]
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _)) (≡-to-≅ (gamma₁ 𝐸 P))) ⟩
         [ S† │ Q ]
      ∎)

   gamma₁ {E = E ᶜ│ Q₀} {E′ ᶜ│ ._} (𝐸 ᵛᵛ│ ._) [ P │ Q ] = cong (λ P → [ P │ Q ]) (gamma₁ 𝐸 P)

   gamma₁ {E = E ᵇ│ _} {E′ = E′ │• .F} (_│•ᵇ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ]
      with step E′ P | inspect (step E′) P
   ... | ◻ , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (tgt E P) | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
   ... | ◻ , P′ | [ ≡P′ ] =
      let S† = tgt ((ᴿ.push *ᶜ) F) ((push *̃) Q); S‡ = tgt F Q in
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) refl refl refl (gamma₁ 𝐸 P)
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡P′))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (tgt E P) | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) |
           step F Q | inspect (step F) Q
   ... | ◻ , P′ | [ ≡P′ ] | ◻ , S‡ | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (ᴬgamma₁ 𝐸 P) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] | ◻ , S‡ | [ ≡S‡ ]
      with step ((ᴿ.push *ᶜ) F) ((push *̃) Q) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | [ ≡S† ] =
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) refl (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 y′ 〉 ᶜ ] , S† | [ ≡S† ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ] | ◻ , P′ | [ ≡P′ ] | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (ᴬgamma₁ 𝐸 P) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (_│•ᵇ_ {y = y} {a = a} 𝐸 F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ] | [ ._ • ᵇ ] , P′ | [ ≡P′ ] | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡S‡ ]
      with step ((ᴿ.push *ᶜ) F) ((push *̃) Q) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | [ ≡S† ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S†)) (trans (sym (renᶜ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S‡)))))
   ... | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , S† | [ ≡S† ] =
      let α : [ • ᴺ.suc x 〈 (push ᴿ̃.*) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†)) in
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ y† y‡ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (sym ([•x〈-〉ᶜ]-inj α)) (gamma₁ 𝐸 P)

   gamma₁ {E = E ᶜ│ Q₀} {E′ = E′ │• .F} (_│•ᶜ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ]
      with step E′ P | step (E′/E (⊖₁ 𝐸)) (tgt E P) | step F Q |
           inspect (step E′) P | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step F) Q
   ... | ◻ , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ (.x •) ᵇ ] , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡S†))))
   ... | [ (.x •) ᵇ ] , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡R′)) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡S†)))))
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ y‡ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)

   gamma₁ {E = P₀ │ᵇ F} {E′ = .E │• F′} (_ᵇ│•_ {y = y} E 𝐹) [ P │ Q ]
      with step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) | step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q) | inspect (step E) P |
           inspect (step ((ᴿ.push *ᵇ) E)) ((push *̃) P)
   ... | ◻ , S′ | ◻ , Q′ | ◻ , R | ◻ , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | _ | _ | [ _ ᵇ ] , R | ◻ , R† | _ | _ | [ ≡R ] | [ ≡R† ] =
      ⊥-elim (◻≢[-] (sym (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R†)))))
   ... | _ | _ | ◻ , R | [ _ ᵇ ] , R† | _ | _ | [ ≡R ] | [ ≡R† ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R†))))
   ... | ◻ , S′ | ◻ , Q′ | [ (x •) ᵇ ] , R | [ (.(ᴺ.suc x) •) ᵇ ] , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | ◻ , S′ | [ • ._ 〈 _ 〉 ᶜ ] , Q′ | _ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ | _ =
      ⊥-elim (◻≢[-] (trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′))))
   ... | [ • _ 〈 _ 〉 ᶜ ] , S′ | ◻ , _ | _ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ | _ =
      ⊥-elim (◻≢[-] (sym (trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′)))))
   ... | [ • x 〈 _ 〉 ᶜ ] , S′ | [ • .(ᴺ.suc x) 〈 _ 〉 ᶜ ] , Q′ | ◻ , R | ◻ , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | [ • x 〈 y‡ 〉 ᶜ ] , S′ | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , Q′ | [ (.x •) ᵇ ] , R | [ .(ᴺ.suc x) • ᵇ ] , R†
       | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      let α : [ • ᴺ.suc x 〈 (push ᴿ̃.*) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′)) in
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α)) (gamma₁ 𝐹 Q)

   gamma₁ {E = P₀ │ᶜ F} {E′ = .E │• F′} (_ᶜ│•_ {y = y} E 𝐹) [ P │ Q ]
      with step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) | step E P |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q) | inspect (step E) P
   ... | ◻ , S′ | ◻ , Q′ | ◻ , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | ◻ , S′ | ◻ , Q′ | [ (x •) ᵇ ] , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | ◻ , S′ | [ _ ] , Q′ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′))))
   ... | [ _ ] , S′ | ◻ , Q′ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡S′)) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′)))))
   ... | [ _ ᶜ ] , S′ | [ _ ᶜ ] , Q′ | ◻ , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | [ • x 〈 y† 〉 ᶜ ] , S′ | [ • .x 〈 y‡ 〉 ᶜ ] , Q′ | [ (.x •) ᵇ ] , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      let α : [ • x 〈 y‡ 〉 ᶜ ] ≡ [ • x 〈 y† 〉 ᶜ ]
          α = trans (sym (,-inj₁ ≡Q′)) (trans (ᴬgamma₁ 𝐹 Q) (,-inj₁ ≡S′)) in
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α)) (gamma₁ 𝐹 Q)

   gamma₁ {E = E ᵇ│ Q₀} {E′ │ᵥ .F} (_│ᵥᵇ_ {x = x} {a = x′ •} 𝐸 F) [ P │ Q ]
      with (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
           step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P |
           inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   ... | id*E/E′ | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
   ... | id*E/E′ | _ , R′ | [ (• ._) ᵇ ] , S | _ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
   ... | id*E/E′ | _ , R′ | ◻ , S | _ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
   ... | id*E/E′ | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ (• ._) ᵇ ] , S′ |
      [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ [ ᴺ.zero ]
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case

   gamma₁ {E = E ᵇ│ Q₀} {E′ │ᵥ .F} (_│ᵥᵇ_ {x = x} {a = • x′} 𝐸 F) [ P │ Q ]
      with (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
           step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P |
           inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   ... | id*E/E′ | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
   ... | id*E/E′ | _ , R′ | [ (• ._) ᵇ ] , S | _ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
   ... | id*E/E′ | _ , R′ | ◻ , S | _ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
   ... | id*E/E′ | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-•x 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-•x 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-•x 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ (• ._) ᵇ ] , S′ |
      [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-•x 𝐸 F P Q P′ S′ id*E/E′ S R′ [ ᴺ.zero ]
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case

   gamma₁ {E = E ᶜ│ Q₀} {E′ │ᵥ .F} (_│ᵥᶜ_ {a = τ} 𝐸 F) [ P │ Q ]
      with (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
           inspect (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P | inspect (step F) Q |
           inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
   ... | id*E/E | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
   ... | id*E/E | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡R′))))
   ... | id*E/E | ◻ , R′ | ◻ , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
   ... | id*E/E | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
   ... | id*E/E | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
   ... | id*E/E | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ [ ᴺ.zero ] ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case

   gamma₁ {E = E ᶜ│ Q₀} {E′ │ᵥ .F} (_│ᵥᶜ_ {a = • x′ 〈 y′ 〉} 𝐸 F) [ P │ Q ]
      with (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
           inspect (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P | inspect (step F) Q |
           inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
   ... | id*E/E | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
   ... | id*E/E | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡R′))))
   ... | id*E/E | ◻ , R′ | ◻ , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-•x〈y〉 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
   ... | id*E/E | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-•x〈y〉 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
   ... | id*E/E | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-•x〈y〉 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
   ... | id*E/E | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
      let open │ᵥᶜ-•x〈y〉 𝐸 F P Q P′ id*E/E S R′ [ ᴺ.zero ] ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
-}

   -- Sub-case 1. tgt (ν• ((idᶠ *) (ᵀ.tgt E) │ᶜ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ])
   gamma₁ {E = P₀ │ᵇ F} {.E │ᵥ F′} (_ᵇ│ᵥ_ {a = • x′} {𝑎 = ˣ∇ˣ} E 𝐹) [ P │ Q ]
      with step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
           inspect (step E) P | inspect (step ((ᴿ.push *ᵇ) E)) ((push *̃) P) |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
   ... | _ , R | _ , R′ | ◻ , S′ | [ • ._ 〈 y 〉 ᶜ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      ⊥-elim (◻≢[-] (trans (cong (residual ˣ∇ˣ) (sym (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′))))
   ... | _ , R | _ , R′ | [ (• ._) ᵇ ] , S′ | ◻ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡Q′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (residual ˣ∇ˣ) (,-inj₁ ≡S′)))))
   ... | ◻ , R | [ _ ] , R′ | _ , S′ | _ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R′))))
   ... | [ ._ • ᵇ ] , R | ◻ , R′ | _ , S′ | _ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (renᵇ-action-comm E push P)) (cong (push ᴬ*̃) (,-inj₁ ≡R)))))
   ... | ◻ , R | ◻ , R′ | ◻ , S′ | ◻ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      let open ᵇ│ᵥ-ˣ∇ˣ E 𝐹 P Q R R′ S′ Q′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R | ◻ , R′ | [ x₁ ] , S′ | [ x₂ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      let open ᵇ│ᵥ-ˣ∇ˣ E 𝐹 P Q R R′ S′ Q′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (gamma₁ 𝐹 Q) in case
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , R′ | ◻ , S′ | ◻ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      let open ᵇ│ᵥ-ˣ∇ˣ E 𝐹 P Q R R′ S′ Q′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (gamma₁ 𝐹 Q) in case
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S′ | [ • ._ 〈 ◻ 〉 ᶜ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      let open ᵇ│ᵥ-ˣ∇ˣ E 𝐹 P Q R R′ S′ Q′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (gamma₁ 𝐹 Q) in
      ⊥-elim ([•x〈[◻]〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (,-inj₁ ≡Q′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (residual ˣ∇ˣ) (,-inj₁ ≡S′)))))
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
      let open ᵇ│ᵥ-ˣ∇ˣ E 𝐹 P Q R R′ S′ Q′ [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (gamma₁ 𝐹 Q) in case

{-
   -- Sub-case 2.
   gamma₁ {E = P₀ │ᵇ F} {.E │ᵥ F′} (_ᵇ│ᵥ_ {a = • x′} {ᵇ∇ᵇ} E 𝐹) [ P │ Q ]
      with step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
                inspect (step E) P | inspect (step ((ᴺ.suc *ᵇ) E)) ((push *̃) P) | inspect (step F′) Q |
                inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
   ... | ◻ , R | [ ._ • ᵇ ] , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡P″))))
   ... | [ ._ • ᵇ ] , R | ◻ , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P″)) (trans (sym (renᵇ-action-comm E push P)) (cong (push ᴬ*̃) (,-inj₁ ≡R)))))
   ... | _ , R | _ , P″ | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
   ... | _ , R | _ , P″ | [ (• ._) ᵇ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S′)))))
   ... | ◻ , R | ◻ , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-•x E 𝐹 P Q R S′ P″ P′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
   ... | ◻ , R | ◻ , P″ | [ _ ] , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-•x E 𝐹 P Q R S′ P″ P′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-•x E 𝐹 P Q R S′ P″ P′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-•x E 𝐹 P Q R S′ P″ P′ [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case

   -- Sub-case 3.
   gamma₁ {E = P₀ │ᵇ F} {.E │ᵥ F′} (_ᵇ│ᵥ_ {a = x′ •} {ᵇ∇ᵇ} E 𝐹) [ P │ Q ]
      with step E P | step ((ᴺ.suc *ᵇ) E) ((push *̃) P) | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
                inspect (step E) P | inspect (step ((ᴺ.suc *ᵇ) E)) ((push *̃) P) | inspect (step F′) Q |
                inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
   ... | ◻ , R | [ ._ • ᵇ ] , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡P″))))
   ... | [ ._ • ᵇ ] , R | ◻ , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P″)) (trans (sym (renᵇ-action-comm E push P)) (cong (push ᴬ*̃) (,-inj₁ ≡R)))))
   ... | _ , R | _ , P″ | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
   ... | _ , R | _ , P″ | [ (• ._) ᵇ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S′)))))
   ... | ◻ , R | ◻ , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-x• E 𝐹 P Q R S′ P″ P′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
   ... | ◻ , R | ◻ , P″ | [ _ ] , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-x• E 𝐹 P Q R S′ P″ P′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-x• E 𝐹 P Q R S′ P″ P′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
   ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
      let open ᵇ│ᵥ-ᵇ∇ᵇ-x• E 𝐹 P Q R S′ P″ P′ [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′) (gamma₁ 𝐹 Q)
      in case
-}

{-
   gamma₁ (E ᶜ│ᵥ 𝐸) P = {!!}
   gamma₁ (𝐸 │• 𝐹) P = {!!}
   gamma₁ (𝐸 │•ᵥ 𝐹) P = {!!}
-}

{-
   gamma₁ {E = E │ᵥ F} {E′ │ᵥ F′} (𝐸 │ᵥ 𝐹) [ P │ Q ]
      with step E′ P | step E P | step F′ Q | step F Q |
           inspect (step E′) P | inspect (step E) P | inspect (step F′) Q | inspect (step F) Q
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | ◻ , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | ◻ , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | ◻ , R′ | [ _ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | ◻ , R′ | [ _ • ᵇ ] , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case zero ◻
   ... | ◻ , R′ | [ _ • ᵇ ] , R | [ (• _) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | ◻ , R′ | [ _ • ᵇ ] , R | [ (• _) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case zero ◻
   ... | [ _ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | [ _ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | [ (• _) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | [ _ • ᵇ ] , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ zero
   ... | [ _ • ᵇ ] , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ zero
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ ◻
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case zero ◻
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case ◻ zero
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case zero zero
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in
      case zero zero

   gamma₁ {E = E │ᵥ F} {E′ │ᵥ F′} (𝐸 │ᵥ′ 𝐹) [ P │ Q ]
      with step E′ P | step E P | step F′ Q | step F Q |
           inspect (step E′) P | inspect (step E) P | inspect (step F′) Q | inspect (step F) Q
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | [ _ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | [ _ • ᵇ ] , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | [ _ • ᵇ ] , R | [ (• _) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | ◻ , R′ | [ _ • ᵇ ] , R | [ (• _) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | [ (• _) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case
   ... | [ _ • ᵇ ] , R′ | [ _ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      let open │ᵥ′ 𝐸 𝐹 P Q R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q) in case

   gamma₁ {E = ν• E} {ν• E′} (ν• 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
      gamma₁-ν• 𝐸 P R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (gamma₁ 𝐸 P)

   -- Sub-case 1.
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 _ 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 2.
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᶜ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 1.
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (x •) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 2.
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = gamma₁-ν•ᵇ 𝐸 P R R′ S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 1.
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 2.
   gamma₁ {a = (x •) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = x • ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 3.
   gamma₁ {a = (• x) ᵇ} {(x′ •) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = (• x) ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ ._ • ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 4.
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
           inspect (step ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ (• ._) ᵇ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᵇ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   gamma₁ {E = νᵇ E} {νᵇ E′} (νˣˣ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {E = νᵇ E} {νᵇ E′} (νˣˣ 𝐸) [ ν P ] | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {E = νᵇ E} {νᵇ E′} (νˣˣ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {E = νᵇ E} {νᵇ E′} (νˣˣ 𝐸) [ ν P ] | [ (• ._) ᵇ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νˣˣ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 1.
   gamma₁ {a = (x •) ᵇ} {• x′ 〈 y 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = x • ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 2.
   gamma₁ {a = (x •) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = x • ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ ._ • ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 3.
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 y 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 _ 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] |
      [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 4.
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ]
      with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
           inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᵇᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
-}

   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      let open •x〈y〉-•x〈y〉 𝐸 P {-(gamma₁ 𝐸 P)-} in {!!} --case

{-
   -- Sub-case 1.
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
       | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ .(ᴺ.suc y′) ] 〉 ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 2.
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 3.
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ]  , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ]  , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ]  , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ]  , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ]  , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ]  , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   -- Sub-case 4.
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | ◻ , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | ◻ , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S | [ τ ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
      gamma₁-νᶜᶜ 𝐸 P R R′ S S′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (gamma₁ 𝐸 P)

   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | ◻ , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ τ ᶜ ] , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
      gamma₁-νᵛᵛ 𝐸 P R R′ S† S‡ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)

   gamma₁ (! 𝐸) [ ! P ] = gamma₁ 𝐸 [ P │ [ ! P ] ]
-}

   gamma₁ _ _ = {!!}
