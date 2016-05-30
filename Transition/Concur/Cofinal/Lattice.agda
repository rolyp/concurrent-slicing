module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; ᴬ⌣-sym; ᴬ⌣-sym-involutive; module _ᴬ⌣_; ᴬ⊖; ᴬγ); open _ᴬ⌣_
   open import Action.Concur.Lattice using (residual)
   open import Action.Lattice as ᴬ̃ using (↓ᵇ⁻_; ↓ᶜ⁻_); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_
   open import Action.Ren.Lattice using () renaming (_* to _ᴬ*̃)
   open import Braiding.Proc using (_⋉̂_)
   open import Braiding.Proc.Lattice using (braid̂)
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; Cxt; _+_)
   open import Name.Lattice as ᴺ̃ using (); open ᴺ̃.↓_
   open import Proc as ᴾ using (Proc; Proc↱; Proc↲); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice using () renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (_ᴿ+_; swap; push; pop; suc)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; Concur; module Concur₁; module Delta′; Delta; ⊖₁; ⊖); open Concur₁
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁; γ)
   open import Transition.Concur.Cofinal.Lattice.Helpers
   open import Transition.Lattice as ᵀ̃ using (step; step⁻; action; target)
   open import Transition.Ren using (_*ᵇ; _*ᶜ)
   open import Transition.Ren.Lattice using (renᶜ-target-comm; renᶜ-action-comm; renᵇ-target-comm; renᵇ-action-comm)

   open Delta′

   private
      coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
                  let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
      coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

      gibble : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) → ↓ π₂ (ᴬ⊖ (ᴬ⌣-sym 𝑎)) → ↓ π₁ (ᴬ⊖ 𝑎)
      gibble 𝑎 rewrite sym (ᴬγ 𝑎) | ᴬ⌣-sym-involutive 𝑎 = idᶠ

   ◻≢[-] : ∀ {Γ} {a : Action Γ} {a′ : ↓⁻ a} → _≡_ {A = ↓_ {A = Action Γ} a} ◻ [ a′ ] → ⊥
   ◻≢[-] ()

   postulate
      ᴬgamma₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
                (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
                action (E′/E (⊖₁ 𝐸)) (target E P′) ≡ gibble 𝑎 (residual (ᴬ⌣-sym 𝑎) (action E′ P′))
--              ×
--              action (E/E′ (⊖₁ 𝐸)) (target E′ P′) ≡ residual 𝑎 (action E P′)

   -- γ₁ lifted to the lattice setting. Can't seem to avoid some use of inspect-on-steroids here, yuk.
   gamma₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
            braiding 𝑎 (γ₁ 𝐸) (target (E′/E (⊖₁ 𝐸)) (target E P′)) ≡ coerceCxt 𝑎 (target (E/E′ (⊖₁ 𝐸)) (target E′ P′))
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
          S† = ≅-trans (≡-to-≅ (sym (renᵇ-target-comm E push P))) (swap∘push̃ _)
          S‡ : (push *̃) (π₂ (step F Q)) ≅ (swap *̃) (π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q)))
          S‡ = ≅-trans (swap∘suc-push̃ _) (≡-to-≅ (cong (swap *̃) (renᵇ-target-comm F push Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (sym (cong₂ _│_ (swap∘push (ᵀ.target E)) (swap∘suc-push (ᵀ.target F))))
                                        [ (push *̃) (π₂ (step E P)) │ π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q)) ]
      ≅⟨ reduce-ᵇ∇ᵇ (sym (cong₂ _│_ (swap∘push (ᵀ.target E)) (swap∘suc-push (ᵀ.target F)))) _ ⟩
         [ (swap *̃) ((push *̃) (π₂ (step E P))) │ (swap *̃) (π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q))) ]
      ≅⟨ ≅-sym ([-│-]-cong (swap∘push (ᵀ.target E)) S† (swap∘suc-push (ᵀ.target F)) S‡) ⟩
         [ π₂ (step ((ᴿ.push *ᵇ) E) ((push *̃) P)) │ (push *̃) (π₂ (step F Q)) ]
      ∎)

   gamma₁ (E ᵇ│ᶜ F) [ P │ Q ] = cong (λ Q′ → [ _ │ Q′ ]) (sym (renᶜ-target-comm F push Q))

   gamma₁ (E ᶜ│ᵇ F) [ P │ Q ] = cong (λ P′ → [ P′ │ _ ]) (renᶜ-target-comm E push P)

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
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹)))))
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
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐹) _)) (≡-to-≅ (gamma₁ 𝐹 Q))) ⟩
         [ (push *̃) P │ S† ]
      ∎)

   gamma₁ {E = _ │ᶜ F} {._ │ᵇ F′} (._ │ᶜᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᵇ (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ≅⟨ reduce-ᶜ∇ᵇ (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐹) _)) (≡-to-≅ (gamma₁ 𝐹 Q))) ⟩
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
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹)))))
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
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸)))))
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
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _)) (≡-to-≅ (gamma₁ 𝐸 P))) ⟩
         [ S† │ (push *̃) Q ]
      ∎)

   gamma₁ {E = E ᶜ│ _} {E′ ᵇ│ ._} (𝐸 ᶜᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ≅⟨ reduce-ᶜ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)) (≡-to-≅ (gamma₁ 𝐸 P))) ⟩
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
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _)) (≡-to-≅ (gamma₁ 𝐸 P))) ⟩
         [ S† │ Q ]
      ∎)

   gamma₁ {E = E ᶜ│ Q₀} {E′ ᶜ│ ._} (𝐸 ᵛᵛ│ ._) [ P │ Q ] = cong (λ P → [ P │ Q ]) (gamma₁ 𝐸 P)

   gamma₁ {E = E ᵇ│ _} {E′ = E′ │• .F} (_│•ᵇ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ] =
      with step E′ P | inspect (step E′) P
   ... | ◻ , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (target E P) | inspect (step (E′/E (⊖₁ 𝐸))) (target E P)
   ... | ◻ , P′ | [ ≡P′ ] =
      let S† = target ((ᴿ.push *ᶜ) F) ((push *̃) Q); S‡ = target F Q in
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) refl refl refl (gamma₁ 𝐸 P)
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡P′))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (target E P) | inspect (step (E′/E (⊖₁ 𝐸))) (target E P) |
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
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†))
          inj : ∀ {Γ} {x y : Name Γ} {y′ y″ : ↓ y} →
                _≡_ {A = ↓_ {A = Action Γ} (• x 〈 y 〉 ᶜ)} [ • x 〈 y′ 〉 ᶜ ] [ • x 〈 y″ 〉 ᶜ ] → y′ ≡ y″
          inj = λ { {y′ = y′} {.y′} refl → refl } in
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ y† y‡ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (sym (inj α)) (gamma₁ 𝐸 P)
-}

   gamma₁ {E = E ᶜ│ Q₀} {E′ = E′ │• .F} (_│•ᶜ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ]
      with step E′ P | step (E′/E (⊖₁ 𝐸)) (target E P) | step F Q |
           inspect (step E′) P | inspect (step (E′/E (⊖₁ 𝐸))) (target E P) | inspect (step F) Q
   ... | ◻ , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ (.x •) ᵇ ] , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ (.x •) ᵇ ] , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] = {!!}
   ... | [ (.x •) ᵇ ] , R′ | ◻ , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ (.x •) ᵇ ] , R′ | ◻ , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] = {!!}
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ y‡ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)

{-
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
{-
   gamma₁ {a = a ᵇ} (_ᵇ│•_ {y = y} {F = F} {F′} E 𝐹) [ P │ Q ] = {!!}
   gamma₁ (E ᶜ│• 𝐸) P₁ = {!!}
   gamma₁ (𝐸 │ᵥᵇ F) P₁ = {!!}
   gamma₁ (𝐸 │ᵥᶜ F) P₁ = {!!}
   gamma₁ (E ᵇ│ᵥ 𝐸) P₁ = {!!}
   gamma₁ (E ᶜ│ᵥ 𝐸) P₁ = {!!}
   gamma₁ (𝐸 │• 𝐸₁) P₁ = {!!}
   gamma₁ (𝐸 │•ᵥ 𝐸₁) P₁ = {!!}1
   gamma₁ (𝐸 │ᵥ• 𝐸₁) P₁ = {!!}
   gamma₁ (𝐸 │ᵥ 𝐸₁) P₁ = {!!}
   gamma₁ (𝐸 │ᵥ′ 𝐸₁) P₁ = {!!}
   gamma₁ (ν• 𝐸) P₁ = {!!}
   gamma₁ (ν•ᵇ 𝐸) P₁ = {!!}
   gamma₁ (ν•ᶜ 𝐸) P₁ = {!!}
   gamma₁ (νᵇᵇ 𝐸) P₁ = {!!}
   gamma₁ (νˣˣ 𝐸) P₁ = {!!}
   gamma₁ (νᵇᶜ 𝐸) P₁ = {!!}
   gamma₁ (νᶜᵇ 𝐸) P₁ = {!!}
   gamma₁ (νᶜᶜ 𝐸) P₁ = {!!}
-}
