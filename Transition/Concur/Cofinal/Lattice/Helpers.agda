module Transition.Concur.Cofinal.Lattice.Helpers where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Ren.Lattice renaming (_* to _ᴬ*̃)
   open import Braiding.Proc.Lattice using (braid̂)
   open import Lattice using (Lattices); open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; Cxt; _+_)
   open import Name.Lattice as ᴺ̃ using (); open ᴺ̃.↓_
   open import Proc as ᴾ using (Proc; Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   open import Proc.Ren.Lattice using () renaming (_* to _*̃)
   open import Ren as ᴿ using (); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (swap; pop; push; _ᴿ+_; suc)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ⊖₁)
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁)
   open import Transition.Lattice using (tgt; action)
   open import Transition.Ren using (_*ᵇ; _*ᶜ)
   open import Transition.Ren.Lattice using (renᵇ-tgt-comm; renᵇ-action-comm; renᶜ-tgt-comm; renᶜ-action-comm)

   open Delta′

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) → ↓ P → ↓ P′
   braiding ˣ∇ˣ eq rewrite eq = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   -- Helpers arise from need to pattern-match on an equality to get braiding to reduce.
   reduce-ˣ∇ˣ : ∀ {Γ P P′} {x u : Name Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ˣ∇ˣ {x = x} {u}) {0} γ P† ≅ P†
   reduce-ˣ∇ˣ refl _ = ≅-refl

   reduce-ᵇ∇ᵇ : ∀ {Γ P P′} {a a′ : Actionᵇ Γ} (γ : ((ᴿ.swap ᴿ.ᴿ+ 0) *) P ≡ P′) (P† : ↓ P) →
                braiding (ᵇ∇ᵇ {a = a} {a′}) {0} γ P† ≅ ((swap ᴿ+ 0) *̃) P†
   reduce-ᵇ∇ᵇ refl _ = ≅-refl

   reduce-ᵇ∇ᶜ : ∀ {Γ P P′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᵇ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᵇ∇ᶜ refl _ = ≅-refl

   reduce-ᶜ∇ᵇ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᶜ∇ᵇ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᶜ∇ᵇ refl _ = ≅-refl

   reduce-ᶜ∇ᶜ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᶜ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᶜ∇ᶜ refl _ = ≅-refl

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

{-
   ᴬgamma₁-│•ᵇ : ∀ {Γ x y P₀ R₀ R′₀ S₀ Q₀} {a : Actionᵇ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ (x •) ᵇ - _ ]→ R′₀}
                (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀) (P : ↓ P₀) (R′ : ↓ R′₀) →
                tgt E′ P ≡ R′ → action (E/E′ (⊖₁ 𝐸)) (tgt E′ P) ≡ (push ᴬ*̃) (action E P) →
                let pop-y*E/E′ = subst (λ a → _ —[ a ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸)))
                                       (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) in
                action pop-y*E/E′ ((pop ◻ *̃) R′) ≡ action E P
   ᴬgamma₁-│•ᵇ {Γ} {x = x} {y} {a = a} {E} {E′} 𝐸 F P R′ ≡R′ IH = ≅-to-≡ (
      let T : Actionᵇ Γ → Set
          T = λ a′ → (ᴿ.pop y *) (ᵀ.tgt E′) —[ a′ ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₂ (⊖₁ 𝐸))
          pop-y*E/E′ = subst T (pop∘push y a) ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸)))
          open ≅-Reasoning in
      begin
         action pop-y*E/E′  ((pop ◻ *̃) R′)
      ≅⟨ ≅-cong✴ T (sym (pop∘push y a)) (λ E† → action E† ((pop ◻ *̃) R′)) (≡-subst-removable T (pop∘push y a) _) ⟩
         action ((ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) ((pop ◻ *̃) R′)
      ≡⟨ sym (renᵇ-action-comm (E/E′ (⊖₁ 𝐸)) (pop ◻) R′) ⟩
         (pop {x₀ = y} ◻ ᴬ*̃) (action (E/E′ (⊖₁ 𝐸)) R′)
      ≡⟨ cong ((pop {x₀ = y} ◻ ᴬ*̃) ∘ᶠ action (E/E′ (⊖₁ 𝐸))) (sym ≡R′) ⟩
         (pop {x₀ = y} ◻ ᴬ*̃) (action (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      ≡⟨ cong (pop {x₀ = y} ◻ ᴬ*̃) IH ⟩
         (pop {x₀ = y} ◻ ᴬ*̃) ((push ᴬ*̃) (action E P))
      ≅⟨ ᴬpop∘push̃ ◻ (action E P) ⟩
         action E P
      ∎)

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
-}

   postulate
    gamma₁-νˣˣ : ∀ {Γ} {x u : Name (Γ + 1)} {P₀ R₀ R′₀} {E : P₀ —[ (• ᴺ.suc x) ᵇ - _ ]→ R₀}
               {E′ : P₀ —[ (• ᴺ.suc u) ᵇ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ˣ∇ˣ ] E′) (S : ↓ (ᴿ.swap *) (tgt₁ (⊖₁ 𝐸)))
                (S′ : ↓ (ᴿ.swap *) (tgt₂ (⊖₁ 𝐸))) →
               (braiding (ˣ∇ˣ {x = x} {u}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸))))
               [ ν S ] ≡ [ ν S′ ]

{-
   gamma₁-νᵛᵛ : ∀ {Γ} {P₀ : Proc (Γ + 1)} {R₀ R′₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ τ ᶜ - _ ]→ R′₀}
               (𝐸 : E ⌣₁[ ᵛ∇ᵛ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀) (S† : ↓ tgt₁ (⊖₁ 𝐸)) (S‡ : ↓ tgt₂ (⊖₁ 𝐸)) →
               tgt E P ≡ R → tgt E′ P ≡ R′ → tgt (E′/E (⊖₁ 𝐸)) R ≡ S† → tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ S‡ →
               braid̂ (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
               _≡_ {A = ↓_ {A = Proc Γ} (ν Proc↱ refl (tgt₂ (⊖₁ 𝐸)))} [ ν braid̂ (γ₁ 𝐸) S† ] [ ν S‡ ]
   gamma₁-νᵛᵛ {E = E} {E′} 𝐸 P R R′ S† S‡ ≡R ≡R′ ≡S† ≡S‡ IH = cong [_] (cong ν_ (
      let open EqReasoning (setoid _) in
      begin
         braid̂ (γ₁ 𝐸) S†
      ≡⟨ cong (braid̂ (γ₁ 𝐸)) (trans (sym ≡S†) (cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R))) ⟩
         braid̂ (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
      ≡⟨ IH ⟩
         tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
      ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
         tgt (E/E′ (⊖₁ 𝐸)) R′
      ≡⟨ ≡S‡ ⟩
         S‡
      ∎))
-}
