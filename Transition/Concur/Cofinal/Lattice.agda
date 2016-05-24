module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; ᴬ⌣-sym; module _ᴬ⌣_; ᴬ⊖; ᴬγ); open _ᴬ⌣_
   open import Action.Concur.Lattice using (residual)
   open import Action.Lattice as ᴬ̃ using (↓ᵇ⁻_; ↓ᶜ⁻_); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_
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
   open import Ren.Lattice using (_ᴿ+_; swap; push; pop)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁)
   open import Transition.Lattice as ᵀ̃ using (step; step⁻; action; target)
   open import Transition.Ren using (_*ᵇ; _*ᶜ)
   open import Transition.Ren.Lattice using (renᶜ-target-comm; renᶜ-action-comm; renᵇ-target-comm; renᵇ-action-comm)

   open Delta′
{-
   ◻≢[-] : ∀ {Γ} {a : Actionᶜ Γ} {a′ : ↓ᶜ⁻ a} → _≡_ {A = ↓_ {A = Action Γ} (a ᶜ)} ◻ [ a′ ᶜ ] → ⊥
   ◻≢[-] ()

   blah : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ → action (E/E′ (⊖₁ 𝐸)) (target E′ P′) ≡ residual 𝑎 (action E P′)
   blah {𝑎 = ˣ∇ˣ} 𝐸 ◻ = refl
   blah {𝑎 = ᵇ∇ᵇ} 𝐸 ◻ = refl
   blah {𝑎 = ᵇ∇ᶜ} 𝐸 ◻ = refl
   blah {𝑎 = ᶜ∇ᵇ} 𝐸 ◻ = refl
   blah {𝑎 = ᶜ∇ᶜ} 𝐸 ◻ = refl
   blah {𝑎 = ᵛ∇ᵛ} 𝐸 ◻ = refl
   blah (E ᵇ│ᵇ F) [ P │ Q ] = sym (ᴬrenᵇ-step-comm E push P)
   blah (E ᵇ│ᶜ F) [ P │ Q ] = refl
   blah (E ᶜ│ᵇ F) [ P │ Q ] = sym (ᴬrenᶜ-step-comm E push P)
   blah (E ᶜ│ᶜ F) [ P │ Q ] = refl
   blah (𝐸 │•ᵇ F) [ P │ Q ] = {!!}

   blah {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , _ | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , _ | _ = refl
   ... | [ τ ᶜ ] , _ | [ eq† ] = ⊥-elim (◻≢[-] (
      let action′ = action (E/E′ (⊖₁ 𝐸)) in
      trans (sym (,-inj₁ eq′)) (trans (sym (blah 𝐸 P)) (trans (cong action′ (,-inj₂ eq)) (,-inj₁ eq†)))))
   blah {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | ◻ , R′ | [ τ ᶜ ] , _ | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , _ | [ eq† ] = ⊥-elim (◻≢[-] (sym (
      let action′ = action (E/E′ (⊖₁ 𝐸)) in
      trans (sym (,-inj₁ eq′)) (trans (sym (blah 𝐸 P)) (trans (cong action′ (,-inj₂ eq)) (,-inj₁ eq†))))))
   ... | [ τ ᶜ ] , _ | [ eq† ] = refl
   blah {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , _ | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , _ | _ = refl
   ... | [ τ ᶜ ] , _ | [ eq† ] = ⊥-elim (◻≢[-] (
      let action′ = action (E/E′ (⊖₁ 𝐸)) in
      trans (sym (,-inj₁ eq′)) (trans (sym (blah 𝐸 P)) (trans (cong action′ (,-inj₂ eq)) (,-inj₁ eq†)))))
   blah {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ τ ᶜ ] , R | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
   ... | ◻ , _ | [ eq† ] = ⊥-elim (◻≢[-] (sym (
      let action′ = action (E/E′ (⊖₁ 𝐸)) in
      trans (sym (,-inj₁ eq′)) (trans (sym (blah 𝐸 P)) (trans (cong action′ (,-inj₂ eq)) (,-inj₁ eq†))))))
   ... | [ τ ᶜ ] , _ | _ = refl
   blah (! 𝐸) [ ! P ] = blah 𝐸 [ P │ [ ! P ] ]
   blah 𝐸 P = {!!}

   blah (𝐸 │•ᶜ F) [ x₁ │ x₂ ] = {!!}
   blah (E ᵇ│• 𝐸) [ x₁ │ x₂ ] = {!!}
   blah (E ᶜ│• 𝐸) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 │ᵥᵇ F) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 │ᵥᶜ F) [ x₁ │ x₂ ] = {!!}
   blah (E ᵇ│ᵥ 𝐸) [ x₁ │ x₂ ] = {!!}
   blah (E ᶜ│ᵥ 𝐸) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 ➕₁ Q) [ x ➕ x₁ ] = {!!}
   blah (P │ᵇᵇ 𝐸) [ x │ x₁ ] = {!!}
   blah (P │ᵇᶜ 𝐸) [ x │ x₁ ] = {!!}
   blah (P │ᶜᵇ 𝐸) [ x │ x₁ ] = {!!}
   blah (P │ᶜᶜ 𝐸) [ x │ x₁ ] = {!!}
   blah (P │ᵛᵛ 𝐸) [ x │ x₁ ] = {!!}
   blah (𝐸 ᵇᵇ│ Q) [ x │ x₁ ] = {!!}
   blah (𝐸 ᵇᶜ│ Q) [ x │ x₁ ] = {!!}
   blah (𝐸 ᶜᵇ│ Q) [ x │ x₁ ] = {!!}
   blah (𝐸 ᶜᶜ│ Q) [ x │ x₁ ] = {!!}
   blah (𝐸 ᵛᵛ│ Q) [ x │ x₁ ] = {!!}
   blah (𝐸 │• 𝐸₁) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 │•ᵥ 𝐸₁) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 │ᵥ• 𝐸₁) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 │ᵥ 𝐸₁) [ x₁ │ x₂ ] = {!!}
   blah (𝐸 │ᵥ′ 𝐸₁) [ x₁ │ x₂ ] = {!!}
   blah (ν• 𝐸) [ ν x₁ ] = {!!}
   blah (ν•ᵇ 𝐸) [ ν x₁ ] = {!!}
   blah (ν•ᶜ 𝐸) [ ν x₁ ] = {!!}
   blah (νᵇᵇ 𝐸) [ ν x ] = {!!}
   blah (νˣˣ 𝐸) [ ν x₁ ] = {!!}
   blah (νᵇᶜ 𝐸) [ ν x ] = {!!}
   blah (νᶜᵇ 𝐸) [ ν x ] = {!!}
   blah (νᶜᶜ 𝐸) [ ν x ] = {!!}
-}
   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} → ⋈̂[ Γ , 𝑎 , Δ ] P P′ → ↓ P → ↓ P′
   braiding ˣ∇ˣ eq rewrite eq = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   -- Most complexity arises from need to pattern-match on an equality to get braiding to reduce.
   private
      coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
                  let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
      coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

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

   -- Not sure of the naming convention to use here. This is essentially γ₁ lifted to the lattice setting.
   gamma₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
            coerceCxt 𝑎 (target (E/E′ (⊖₁ 𝐸)) (target E′ P′)) ≡ braiding 𝑎 (γ₁ 𝐸) (target (E′/E (⊖₁ 𝐸)) (target E P′))
{-
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _))))) (≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _)))
   gamma₁ {𝑎 = ᵇ∇ᵇ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _))))) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)))
   gamma₁ {𝑎 = ᵇ∇ᶜ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _))))) (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _)))
   gamma₁ {𝑎 = ᶜ∇ᵇ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _))))) (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)))
   gamma₁ {𝑎 = ᶜ∇ᶜ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (◻-cong (sym (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _))))) (≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _)))
   gamma₁ {𝑎 = ᵛ∇ᵛ} 𝐸 ◻ = refl
   gamma₁ {a = a ᵇ} {a′ ᵇ} {E = .E ᵇ│ Q₀} {E′ = P₀ │ᵇ .F} (E ᵇ│ᵇ F) [ P │ Q ] =
      let S† : π₂ (step ((ᴿ.push *ᵇ) E) ((push *̃) P)) ≅ (swap *̃) ((push *̃) (π₂ (step E P)))
          S† = ≅-trans (≡-to-≅ (sym (renᵇ-step-comm E push P))) (swap∘push̃ _)
          S‡ : (push *̃) (π₂ (step F Q)) ≅ (swap *̃) (π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q)))
          S‡ = ≅-trans (swap∘suc-push̃ _) (≡-to-≅ (cong (swap *̃) (renᵇ-step-comm F push Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ π₂ (step ((ᴿ.push *ᵇ) E) ((push *̃) P)) │ (push *̃) (π₂ (step F Q)) ]
      ≅⟨ [-│-]-cong (swap∘push (ᵀ.target E)) S† (swap∘suc-push (ᵀ.target F)) S‡ ⟩
         [ (swap *̃) ((push *̃) (π₂ (step E P))) │ (swap *̃) (π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q))) ]
      ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (sym (cong₂ _│_ (swap∘push (ᵀ.target E)) (swap∘suc-push (ᵀ.target F)))) _) ⟩
         braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (sym (cong₂ _│_ (swap∘push (ᵀ.target E)) (swap∘suc-push (ᵀ.target F))))
                                        [ (push *̃) (π₂ (step E P)) │ π₂ (step ((ᴿ.push *ᵇ) F) ((push *̃) Q)) ]
      ∎)
   gamma₁ (E ᵇ│ᶜ F) [ P │ Q ] = cong (λ Q′ → [ _ │ Q′ ]) (renᶜ-step-comm F push Q)
   gamma₁ (E ᶜ│ᵇ F) [ P │ Q ] = cong (λ P′ → [ P′ │ _ ]) (sym (renᶜ-step-comm E push P))
   gamma₁ (E ᶜ│ᶜ F) [ P │ Q ] = refl
   gamma₁ (𝐸 ➕₁ Q) [ P ➕ _ ] = gamma₁ 𝐸 P
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = _ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐹)) (π₂ (step F′ Q)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐹)) (π₂ (step F Q)))
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
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ S† │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (sym (≅-to-≡ (Proc↲ refl (S′ (⊖₁ 𝐸))))) (sym (γ₁ 𝐸)))
                     (≅-trans (≡-to-≅ (gamma₁ 𝐸 P)) (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _)) ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x} {u} (cong₂ _│_ (γ₁ 𝐸) refl) _) ⟩
         braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ∎)
   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
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
      let S† = π₂ (step (E/E′ (⊖₁ 𝐸)) (π₂ (step E′ P)))
          S‡ = π₂ (step (E′/E (⊖₁ 𝐸)) (π₂ (step E P)))
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
-}
   gamma₁ {E = E ᵇ│ Q₀} {E′ = E′ │• .F} (_│•ᵇ_ {y = y} {a = a} 𝐸 F) [ P │ Q ] with (ᴿ.pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a
      with step E′ P | step F Q | inspect (step E′) P | inspect (step F) Q
   ... | ◻ , R | _ , R′ | [ eq ] | [ eq′ ]
      with step (E′/E (⊖₁ 𝐸)) (target E P) | step ((ᴿ.push *ᶜ) F) ((push *̃) Q) |
           inspect (step (E′/E (⊖₁ 𝐸))) (target E P) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | _ , S‡ | [ eq† ] | [ eq‡ ] =
      let blah = cong₂ _│_ (
            let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
            begin _ ≡⟨ cong (ᴿ.pop (ᴿ.push y) *) (swap-swap (γ₁ 𝐸)) ⟩ _ ≡⟨ sym (pop∘swap y S′) ⟩ _ ∎
            ) refl
          quib : (push *̃) R′ ≡ S‡
          quib = trans (cong (push *̃) (sym (,-inj₂ eq′))) (trans (renᶜ-target-comm F push Q) (,-inj₂ eq‡))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         [ target pop-y*E/E′ ((pop ◻ *̃) R) │ (push *̃) R′ ]
      ≅⟨ [-│-]-cong {!!} {!!} refl (≡-to-≅ quib) ⟩
         [ (pop ◻ *̃) S† │ S‡ ]
      ≅⟨ {!!} ⟩
         braiding ᵇ∇ᶜ blah [ (pop ◻ *̃) S† │ S‡ ]
      ∎)
   ... | [ (◻ •) ᵇ ] , _ | ◻ , _ | [ eq† ] | [ eq‡ ]  = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | ◻ , _ | [ eq† ] | [ eq‡ ]  = {!!}
   ... | [ (◻ •) ᵇ ] , _ | _ , _ | [ eq† ] | [ eq‡ ]  = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ eq† ] | [ eq‡ ]  = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ | [ eq† ] | [ eq‡ ]  = {!!}
   gamma₁ {E = E ᵇ│ Q₀} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] | _ | [ (◻ •) ᵇ ] , _ | _ , _ | [ eq ] | [ eq′ ] = {!!}
{-
      with step (E′/E (⊖₁ 𝐸)) (target E P) | step ((ᴿ.push *ᶜ) F) ((push *̃) Q)
   ... | ◻ , _ | _ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | _ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ = {!!}
-}
   gamma₁ {E = E ᵇ│ Q₀} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] | _ | [ ([ x ] •) ᵇ ] , _ | ◻ , _ | [ eq ] | [ eq′ ] = {!!}
{-
      with step (E′/E (⊖₁ 𝐸)) (target E P) | step ((ᴿ.push *ᶜ) F) ((push *̃) Q)
   ... | ◻ , _ | _ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | _ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ = {!!}
-}
   gamma₁ {E = E ᵇ│ Q₀} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] | _ | [ ([ x ] •) ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ eq ] | [ eq′ ] = {!!}
{-
      with step (E′/E (⊖₁ 𝐸)) (target E P) | step ((ᴿ.push *ᶜ) F) ((push *̃) Q)
   ... | ◻ , _ | _ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | _ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ = {!!}
-}
   gamma₁ {E = E ᵇ│ Q₀} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] | _ | [ ([ x ] •) ᵇ ] , _ | [ • [ .x ] 〈 _ 〉 ᶜ ] , _ | [ eq ] | [ eq′ ] = {!!}
{-
      with step (E′/E (⊖₁ 𝐸)) (target E P) | step ((ᴿ.push *ᶜ) F) ((push *̃) Q)
   ... | ◻ , _ | _ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | ◻ , _ = {!!}
   ... | [ (◻ •) ᵇ ] , _ | _ , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ = {!!}
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ = {!!}
-}
{-
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ]
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , R | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , S′ | ◻ , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | ◻ , S′ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | ◻ , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | ◻ , R′ | [ τ ᶜ ] , R | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , S′ | ◻ , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | ◻ , S′ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | ◻ , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | ◻ , R | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , _ | ◻ , _ | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | ◻ , _ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | ◻ , _ | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] | [ τ ᶜ ] , R′ | [ τ ᶜ ] , R | [ eq ] | [ eq′ ]
      with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
   ... | ◻ , _ | ◻ , _ | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | ◻ , _ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | ◻ , _ | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   ... | [ τ ᶜ ] , S′ | [ τ ᶜ ] , S | [ eq† ] | [ eq‡ ] = cong [_] (cong ν_ (
      trans (sym (,-inj₂ eq†))
            (trans (cong (target (E/E′ (⊖₁ 𝐸))) (sym (,-inj₂ eq)))
                   (trans (gamma₁ 𝐸 P)
                          (cong (braid̂ (γ₁ 𝐸)) (trans (cong (target (E′/E (⊖₁ 𝐸))) (,-inj₂ eq′)) (,-inj₂ eq‡)))))))
   gamma₁ (! 𝐸) [ ! P ] = gamma₁ 𝐸 [ P │ [ ! P ] ]
-}
   gamma₁ _ _ = {!!}
{-
   gamma₁ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) [ P │ Q ] = {!!}
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
