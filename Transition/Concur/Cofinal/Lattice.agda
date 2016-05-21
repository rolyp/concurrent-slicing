module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; inc); open ᴬ.Action
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬγ); open _ᴬ⌣_
   open import Action.Lattice as ᴬ̃ using (); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; Cxt; _+_)
   open import Name.Lattice as ᴺ̃ using (); open ᴺ̃.↓_
   open import Proc as ᴾ using (Proc; Proc↱; Proc↲); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice using () renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (_ᴿ+_; swap; push)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁)
   open import Transition.Lattice using (fwd; step)
   open import Transition.Ren using (_*ᵇ; _*ᶜ)
   open import Transition.Ren.Lattice using (renᶜ-fwd-comm; renᵇ-fwd-comm)

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} → ⋈̂[ Γ , 𝑎 , Δ ] P P′ → ↓ P → ↓ P′
   braiding ˣ∇ˣ eq rewrite eq = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   open Delta′

   -- Most complexity arises from need to pattern-match on an equality to get braiding to reduce.
   private
      coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
                  let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
      coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

      reduce-ᶜ∇ᶜ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                   braiding (ᶜ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
      reduce-ᶜ∇ᶜ refl _ = ≅-refl

      reduce-ᵇ∇ᶜ : ∀ {Γ P P′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                   braiding (ᵇ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
      reduce-ᵇ∇ᶜ refl _ = ≅-refl

      reduce-ᶜ∇ᵇ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                   braiding (ᶜ∇ᵇ {a = a} {a′}) {0} γ P† ≅ P†
      reduce-ᶜ∇ᵇ refl _ = ≅-refl

      reduce-ᵇ∇ᵇ : ∀ {Γ P P′} {a a′ : Actionᵇ Γ} (γ : ((ᴿ.swap ᴿ.ᴿ+ 0) *) P ≡ P′) (P† : ↓ P) →
                   braiding (ᵇ∇ᵇ {a = a} {a′}) {0} γ P† ≅ ((swap ᴿ+ 0) *̃) P†
      reduce-ᵇ∇ᵇ refl _ = ≅-refl

      reduce-ˣ∇ˣ : ∀ {Γ P P′} {x u : Name Γ} (γ : P ≡ P′) (P† : ↓ P) →
                   braiding (ˣ∇ˣ {x = x} {u}) {0} γ P† ≅ P†
      reduce-ˣ∇ˣ refl _ = ≅-refl

      ◻-cong : ∀ {Γ} {P₀ P₁ : Proc Γ} → P₀ ≡ P₁ →
               _≅_ {A = ↓_ {A = Proc Γ} _} (◻ {P = P₀}) {↓_ {A = Proc Γ} _} (◻ {P = P₁})
      ◻-cong refl = ≅-refl

      [-│]-cong : ∀ {Γ} {P₀ P₁ Q₀ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₁} (Q : ↓ Q₀) → P₀ ≡ P₁ → P ≅ P′ →
                  _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P′ │ Q ]
      [-│]-cong _ refl ≅-refl = ≅-refl

      [│-]-cong : ∀ {Γ} {P₀ Q₀ Q₁ : Proc Γ} (P : ↓ P₀) {Q : ↓ Q₀} {Q′ : ↓ Q₁} → Q₀ ≡ Q₁ → Q ≅ Q′ →
                  _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P │ Q′ ]
      [│-]-cong _ refl ≅-refl = ≅-refl

      [-│-]-cong : ∀ {Γ} {P₀ P₁ Q₀ Q₁ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₁} {Q : ↓ Q₀} {Q′ : ↓ Q₁} →
                   P₀ ≡ P₁ → P ≅ P′ → Q₀ ≡ Q₁ → Q ≅ Q′ →
                   _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P′ │ Q′ ]
      [-│-]-cong refl ≅-refl refl ≅-refl = ≅-refl

   -- Not sure of the naming convention to use here. This is essentially γ₁ lifted to the lattice setting.
   gamma₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
            coerceCxt 𝑎 (π₂ (fwd (E/E′ (⊖₁ 𝐸)) (π₂ (fwd E′ P′)))) ≡
            braiding 𝑎 (γ₁ 𝐸) (π₂ (fwd (E′/E (⊖₁ 𝐸)) (π₂ (fwd E P′))))
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} 𝐸 ◻ =
      let open ≅-Reasoning in ≅-to-≡ (
      begin
         ◻
      ≅⟨ ◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))) ⟩
         ◻
      ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _) ⟩
         braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐸) (◻ {P = S (⊖₁ 𝐸)})
      ∎)
   gamma₁ {𝑎 = ᵇ∇ᵇ} 𝐸 ◻ =
      let open ≅-Reasoning in ≅-to-≡ (
      begin
         ◻
      ≅⟨ ◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))) ⟩
         ◻
      ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) ⟩
         braiding ᵇ∇ᵇ {0} (γ₁ 𝐸) (◻ {P = S (⊖₁ 𝐸)})
      ∎)
   gamma₁ {𝑎 = ᵇ∇ᶜ} 𝐸 ◻ =
      let open ≅-Reasoning in ≅-to-≡ (
      begin
         ◻
      ≅⟨ ◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))) ⟩
         ◻
      ≅⟨ ≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _) ⟩
         braiding ᵇ∇ᶜ {0} (γ₁ 𝐸) (◻ {P = S (⊖₁ 𝐸)})
      ∎)
   gamma₁ {𝑎 = ᶜ∇ᵇ} 𝐸 ◻ =
      let open ≅-Reasoning in ≅-to-≡ (
      begin
         ◻
      ≅⟨ ◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))) ⟩
         ◻
      ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _) ⟩
         braiding ᶜ∇ᵇ {0} (γ₁ 𝐸) (◻ {P = S (⊖₁ 𝐸)})
      ∎)
   gamma₁ {𝑎 = ᶜ∇ᶜ} 𝐸 ◻ =
      let open ≅-Reasoning in ≅-to-≡ (
      begin
         ◻
      ≅⟨ ◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))) ⟩
         ◻
      ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _) ⟩
         braiding ᶜ∇ᶜ {0} (γ₁ 𝐸) (◻ {P = S (⊖₁ 𝐸)})
      ∎)
   gamma₁ {𝑎 = ᵛ∇ᵛ} {E = E} {E′} 𝐸 ◻ = refl
   gamma₁ {a = a ᵇ} {a′ ᵇ} {E = .E ᵇ│ Q₀} {E′ = P₀ │ᵇ .F} (E ᵇ│ᵇ F) [ P │ Q ] =
      let S† : π₂ (fwd ((ᴿ.push *ᵇ) E) ((push *̃) P)) ≅ (swap *̃) ((push *̃) (π₂ (fwd E P)))
          S† = ≅-trans (≡-to-≅ (sym (renᵇ-fwd-comm E push P))) (swap∘push̃ _)
          S‡ : (push *̃) (π₂ (fwd F Q)) ≅ (swap *̃) (π₂ (fwd ((ᴿ.push *ᵇ) F) ((push *̃) Q)))
          S‡ = ≅-trans (swap∘suc-push̃ _) (≡-to-≅ (cong (swap *̃) (renᵇ-fwd-comm F push Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ π₂ (fwd ((ᴿ.push *ᵇ) E) ((push *̃) P)) │ (push *̃) (π₂ (fwd F Q)) ]
      ≅⟨ [-│-]-cong (swap∘push (target E)) S† (swap∘suc-push (target F)) S‡ ⟩
         [ (swap *̃) ((push *̃) (π₂ (fwd E P))) │ (swap *̃) (π₂ (fwd ((ᴿ.push *ᵇ) F) ((push *̃) Q))) ]
      ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (sym (cong₂ _│_ (swap∘push (target E)) (swap∘suc-push (target F)))) _) ⟩
         braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (sym (cong₂ _│_ (swap∘push (target E)) (swap∘suc-push (target F))))
                                        [ (push *̃) (π₂ (fwd E P)) │ π₂ (fwd ((ᴿ.push *ᵇ) F) ((push *̃) Q)) ]
      ∎)
   gamma₁ (E ᵇ│ᶜ F) [ P │ Q ] = cong (λ Q′ → [ _ │ Q′ ]) (renᶜ-fwd-comm F push Q)
   gamma₁ (E ᶜ│ᵇ F) [ P │ Q ] = cong (λ P′ → [ P′ │ _ ]) (sym (renᶜ-fwd-comm E push P))
   gamma₁ (E ᶜ│ᶜ F) [ P │ Q ] = refl
   gamma₁ (𝐸 ➕₁ Q) [ P ➕ _ ] = gamma₁ 𝐸 P
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = _ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐹)) (π₂ (fwd F′ Q)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐹)) (π₂ (fwd F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ (push *̃) P │ S† ]
      ≅⟨ [│-]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹))))) (sym (γ₁ 𝐹)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐹 Q)) (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐹) _)) ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x} {u} (cong₂ _│_ refl (γ₁ 𝐹)) _) ⟩
         braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ∎)
   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = P₀ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐹)) (π₂ (fwd F′ Q)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐹)) (π₂ (fwd F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ (push *̃) ((push *̃) P) │ S† ]
      ≅⟨ [-│-]-cong (sym (swap∘push∘push P₀)) (≅-sym (swap∘push∘push̃ P))
                    (sym (γ₁ 𝐹)) (≅-trans (≡-to-≅ (gamma₁ 𝐹 Q)) (reduce-ᵇ∇ᵇ (γ₁ 𝐹) S‡)) ⟩
         [ (swap *̃) ((push *̃) ((push *̃) P)) │ (swap *̃) S‡ ]
      ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (cong₂ _│_ (swap∘push∘push P₀) (γ₁ 𝐹)) _) ⟩
         braiding ᵇ∇ᵇ {0} (cong₂ _│_ (swap∘push∘push P₀) (γ₁ 𝐹)) [ (push *̃) ((push *̃) P) │ S‡ ]
      ∎)
   gamma₁ {E = _ │ᵇ F} {._ │ᶜ F′} (._ │ᵇᶜ 𝐹) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐹)) (π₂ (fwd F′ Q)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐹)) (π₂ (fwd F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ (push *̃) P │ S† ]
      ≅⟨ [│-]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹))))) (sym (γ₁ 𝐹)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐹 Q)) (reduce-ᵇ∇ᶜ (γ₁ 𝐹) _)) ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ ≅-sym (reduce-ᵇ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _) ⟩
         braiding ᵇ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ∎)
   gamma₁ {E = _ │ᶜ F} {._ │ᵇ F′} (._ │ᶜᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐹)) (π₂ (fwd F′ Q)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐹)) (π₂ (fwd F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ (push *̃) P │ S† ]
      ≅⟨ [│-]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹))))) (sym (γ₁ 𝐹)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐹 Q)) (reduce-ᶜ∇ᵇ (γ₁ 𝐹) _)) ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (cong₂ _│_ refl (γ₁ 𝐹)) _) ⟩
         braiding ᶜ∇ᵇ (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ∎)
   gamma₁ {E = _ │ᶜ F} {._ │ᶜ F′} (._ │ᶜᶜ 𝐹) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐹)) (π₂ (fwd F′ Q)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐹)) (π₂ (fwd F Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ P │ S† ]
      ≅⟨ [│-]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐹))))) (sym (γ₁ 𝐹)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐹 Q)) (reduce-ᶜ∇ᶜ (γ₁ 𝐹) _)) ⟩
         [ P │ S‡ ]
      ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _) ⟩
         braiding ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ P │ S‡ ]
      ∎)
   gamma₁ {E = P₀ │ᶜ F} {._ │ᶜ F′} (._ │ᵛᵛ 𝐹) [ P │ Q ] = cong (λ Q → [ P │ Q ]) (gamma₁ 𝐹 Q)
   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐸)) (π₂ (fwd E′ P)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐸)) (π₂ (fwd E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ S† │ (push *̃) ((push *̃) Q) ]
      ≅⟨ [-│-]-cong (sym (γ₁ 𝐸)) (≅-trans (≡-to-≅ (gamma₁ 𝐸 P)) (reduce-ᵇ∇ᵇ (γ₁ 𝐸) S‡))
                    (sym (swap∘push∘push Q₀)) (≅-sym (swap∘push∘push̃ Q)) ⟩
         [ (swap *̃) S‡ │ (swap *̃) ((push *̃) ((push *̃) Q)) ]
      ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀)) _) ⟩
         braiding ᵇ∇ᵇ {0} (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀)) [ S‡ │ (push *̃) ((push *̃) Q) ]
      ∎)
   gamma₁ {E = E ᵇ│ _} {E′ ᶜ│ ._} (𝐸 ᵇᶜ│ ._) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐸)) (π₂ (fwd E′ P)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐸)) (π₂ (fwd E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ S† │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸))))) (sym (γ₁ 𝐸)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐸 P)) (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _)) ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ ≅-sym (reduce-ᵇ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) _) ⟩
         braiding ᵇ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ∎)
   gamma₁ {E = E ᶜ│ _} {E′ ᵇ│ ._} (𝐸 ᶜᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐸)) (π₂ (fwd E′ P)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐸)) (π₂ (fwd E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ S† │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸))))) (sym (γ₁ 𝐸)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐸 P)) (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)) ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) refl) _) ⟩
         braiding ᶜ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ∎)
   gamma₁ {E = E ᶜ│ _} {E′ ᶜ│ ._} (𝐸 ᶜᶜ│ ._) [ P │ Q ] =
      let S† = π₂ (fwd (E/E′ (⊖₁ 𝐸)) (π₂ (fwd E′ P)))
          S‡ = π₂ (fwd (E′/E (⊖₁ 𝐸)) (π₂ (fwd E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ S† │ Q ]
      ≅⟨ [-│]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸))))) (sym (γ₁ 𝐸)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐸 P)) (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _)) ⟩
         [ S‡ │ Q ]
      ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) _) ⟩
         braiding ᶜ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │  Q ]
      ∎)
   gamma₁ {E = E ᶜ│ Q₀} {E′ ᶜ│ ._} (𝐸 ᵛᵛ│ ._) [ P │ Q ] = cong (λ P → [ P │ Q ]) (gamma₁ 𝐸 P)
   gamma₁ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) [ P │ Q ] with (ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | _ rewrite pop∘push y a = {!!}
   gamma₁ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) [ P │ Q ] with (ᴿ.pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | _ rewrite pop∘push y a = {!!}
   gamma₁ {a = a ᵇ} (_ᵇ│•_ {y = y} {F = F} {F′} E 𝐹) [ P │ Q ]
      with π₁ (fwd E P) | π₁ (fwd F′ Q) | π₁ (fwd ((ᴿ.push *ᵇ) E) ((push *̃) P)) | π₁ (fwd  (E′/E (⊖₁ 𝐹)) (π₂ (fwd F Q)))
   ... | ◻ | _ | ◻ | _ =
      let open ≅-Reasoning in ≅-to-≡ (
      begin
         ◻
      ≅⟨ ◻-cong (cong₂ _│_ (pop∘suc-push y (target E)) (sym (γ₁ 𝐹))) ⟩
         ◻
      ≅⟨ ≅-sym (reduce-ᵇ∇ᶜ (cong₂ _│_ (sym (pop∘suc-push y (target E))) (γ₁ 𝐹)) _)  ⟩
         braiding ᵇ∇ᶜ (cong₂ _│_ (sym (pop∘suc-push y (target E))) (γ₁ 𝐹)) ◻
      ∎)
   ... | ◻ | b | [ x₁ ] | d = {!!}
   ... | [ x₁ ] | b | c | d = {!!}
   gamma₁ 𝐸 P = {!!}
{-
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
   gamma₁ (νᵛᵛ 𝐸) P₁ = {!!}
   gamma₁ (! 𝐸) P₁ = {!!}
-}
