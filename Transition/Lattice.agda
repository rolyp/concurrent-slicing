module Transition.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; module Action; Actionᵇ; module Actionᵇ; Actionᶜ; module Actionᶜ);
      open Action; open Actionᵇ; open Actionᶜ
   import Action.Lattice as ᴬ̃;
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ_; open ᴬ̃._≤ᶜ_
   open import Action.Ren
   open import Lattice using (Lattices; Prefixes); open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Name as ᴺ using (Name; _+_)
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Proc as ᴾ using (Proc; module Proc); open ᴾ.Proc
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (_*ᴹ; unren; unrenᴹ) renaming (_* to _*̃)
   open import Ren as ᴿ using (module Renameable); open Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (_̃_; pop; popᴹ; repl; replᴹ; push; swap)
   open import Transition as ᵀ using (_—[_-_]→_; module _—[_-_]→_); open _—[_-_]→_

   open module Action×Proc {Γ} = Lattice.Product (Action Γ) (Proc ∘ᶠ ᴬ.tgt) using (×-prefixes)

   -- Seem to need this to coerce product lattice to more specific type.
   instance
      ᴬᴾ-prefixes : ∀ {Γ} → Lattice.Prefixes (Σ[ a ∈ Action Γ ] Proc (ᴬ.tgt a))
      ᴬᴾ-prefixes = ×-prefixes

   -- These should probably move to Ren.Lattice.
   id-elim : ∀ {Γ} {P₀ : Proc Γ} (P : ↓ (idᶠ *) P₀) → ↓ P₀
   id-elim {P₀ = P₀} = subst ↓_ (*-preserves-id P₀)

   id-elimᴹ : ∀ {Γ} {P₀ : Proc Γ} {P P′ : ↓ (idᶠ *) P₀} → P ≤ P′ →
              subst ↓_ (*-preserves-id P₀) P ≤ subst ↓_ (*-preserves-id P₀) P′
   id-elimᴹ {P₀ = P₀} {P} {P′} =
      ≅-subst✴₂ ↓_ _≤_ (*-preserves-id P₀)
         (≅-sym (≡-subst-removable ↓_ (*-preserves-id P₀) P))
         (≅-sym (≡-subst-removable ↓_ (*-preserves-id P₀) P′))

   id-intro : ∀ {Γ} {P₀ : Proc Γ} (P : ↓ P₀) → ↓ (idᶠ *) P₀
   id-intro {P₀ = P₀} = subst ↓_ (sym (*-preserves-id P₀))

   id-introᴹ : ∀ {Γ} {P₀ : Proc Γ} {P P′ : ↓ P₀} → P ≤ P′ →
               subst ↓_ (sym (*-preserves-id P₀)) P ≤ subst ↓_ (sym (*-preserves-id P₀)) P′
   id-introᴹ {P₀ = P₀} {P} {P′} =
      ≅-subst✴₂ ↓_ _≤_ (sym (*-preserves-id P₀))
         (≅-sym (≡-subst-removable ↓_ (sym (*-preserves-id P₀)) P))
         (≅-sym (≡-subst-removable ↓_ (sym (*-preserves-id P₀)) P′))

   step : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ P → ↓ ᵀ.out E
   step⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻ P → ↓ ᵀ.out E

   step E [ P ] = step⁻ E P
   step E ◻ = ◻ , ◻

   step⁻ (x •∙ _) (.x •∙ P) = [ (x •) ᵇ ] , P
   step⁻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉∙ P) = [ • x 〈 y 〉 ᶜ ] , P
   step⁻ (E ➕₁ _) (P ➕ Q) = step E P
   step⁻ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = let a , R = step E P in a , [ R │ (push *̃) Q ]
   step⁻ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = let a , R = step E P in a , [ R │ Q ]
   step⁻ {a = _ ᵇ} (_ │ᵇ F) (P │ Q) = let a , S = step F Q in a , [ (push *̃) P │ S ]
   step⁻ {a = _ ᶜ} (_ │ᶜ F) (P │ Q) = let a , S = step F Q in a , [ P │ S ]
   step⁻ (E │• F) (P │ Q) with step E P | step F Q
   ... | [ (x •) ᵇ ] , R | [ • .x 〈 y 〉 ᶜ ] , S = [ τ ᶜ ] , [ (pop y *̃) R │ S ]
   ... | ◻ , R | [ • ._ 〈 y 〉 ᶜ ] , S = ◻ , [ (pop y *̃) R │ S ]
   ... | _ , R | _ , S = ◻ , [ (pop ◻ *̃) R │ S ]
   step⁻ (E │ᵥ F) (P │ Q) with step E P | step F Q
   ... | ◻ , R | [ • x ﹙ y ﹚ ᵇ ] , S =
      ◻ , [ ν [ id-elim ((repl y *̃) R) │ S ] ]
   ... | [ x • ᵇ ] , R | [ • .x ﹙ y ﹚ ᵇ ] , S =
      [ τ ᶜ ] , [ ν [ id-elim ((repl y *̃) R) │ S ] ]
   ... | _ , R | _ , S = ◻ , [ ν [ id-elim ((repl ◻ *̃) R) │ S ] ]
   step⁻ (ν•_ {x = x} E) (ν P) with step E P
   ... | [ • .(ᴺ.suc x) 〈 ◻ 〉 ᶜ ] , R = [ (• x ﹙ ◻ ﹚) ᵇ ] , R
   ... | [ • .(ᴺ.suc x) 〈 [ .ᴺ.zero ] 〉 ᶜ ] , R = [ (• x ﹙ zero ﹚) ᵇ ] , R
   ... | _ , R = ◻ , R
   step⁻ {a = x • ᵇ} (νᵇ E) (ν P) with step E P
   ... | [ .(ᴺ.suc x) • ᵇ ] , R = [ x • ᵇ ] , [ ν (swap *̃) R ]
   ... | ◻ , R = ◻ , [ ν (swap *̃) R ]
   step⁻ {a = (• x) ᵇ} (νᵇ E) (ν P) with step E P
   ... | [ (• .(ᴺ.suc x) ﹙ [ .ᴺ.zero ] ﹚ ) ᵇ ] , R = [ • x ﹙ zero ﹚ ᵇ ] ,  [ ν (swap *̃) R ]
   ... | [ (• .(ᴺ.suc x) ﹙ ◻ ﹚ ) ᵇ ] , R = [ • x ﹙ ◻ ﹚ ᵇ ] ,  [ ν (swap *̃) R ]
   ... | ◻ , R = ◻ , [ ν (swap *̃) R ]
   step⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (ν P) with step E P
   ... | [ • .(ᴺ.suc x) 〈 [ .(ᴺ.suc y) ] 〉 ᶜ ] , R = [ • x 〈 [ y ] 〉 ᶜ ] , [ ν R ]
   ... | [ • .(ᴺ.suc x) 〈 ◻ 〉 ᶜ ] , R = [ • x 〈 ◻ 〉 ᶜ ] , [ ν R ]
   ... | ◻ , R = ◻ , [ ν R ]
   -- Explicitly match the action to translate it by (- 1).
   step⁻ {a = τ ᶜ} (νᶜ E) (ν P) with step E P
   ... | [ τ ᶜ ] , R = [ τ ᶜ ] , [ ν R ]
   ... | ◻ , R = ◻ , [ ν R ]
   step⁻ (! E) (! P) = step E [ P │ [ ! P ] ]

   stepᴹ : ∀ {Γ P₀} {a : Action Γ} {P′} (E : P₀ —[ a - _ ]→ P′) {P P′ : ↓ P₀} → P ≤ P′ → step E P ≤ step E P′
   step⁻ᴹ : ∀ {Γ P₀} {a : Action Γ} {P′} (E : P₀ —[ a - _ ]→ P′) {P P′ : ↓⁻ P₀} → P ≤⁻ P′ → step⁻ E P ≤ step⁻ E P′

   stepᴹ E [ P ] = step⁻ᴹ E P
   stepᴹ E ◻ = ◻ , ◻

   step⁻ᴹ (x •∙ _) (.x •∙ P) = [ (x •) ᵇ ] , P
   step⁻ᴹ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉∙ P) = [ • x 〈 y 〉 ᶜ ] , P
   step⁻ᴹ (E ➕₁ _) (P ➕ Q) = stepᴹ E P
   step⁻ᴹ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = let a , R = stepᴹ E P in a , [ R │ (ᴹ push *ᴹ) Q ]
   step⁻ᴹ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = let a , R = stepᴹ E P in a , [ R │ Q ]
   step⁻ᴹ {a = _ ᵇ} (_ │ᵇ F) (P │ Q) = let a , S = stepᴹ F Q in a , [ (ᴹ push *ᴹ) P │ S ]
   step⁻ᴹ {a = _ ᶜ} (_ │ᶜ F) (P │ Q) = let a , S = stepᴹ F Q in a , [ P │ S ]

   step⁻ᴹ (E │• F) {P │ Q} {P′ │ Q′} (P† │ Q†)
      with step E P | step E P′ | stepᴹ E P† | step F Q | step F Q′ | stepᴹ F Q†
   ... | [ _ ] , _ | ◻ , _ | () , _ | _ | _ | _
   ... | _ | _ | _ | [ _ ] , _ | ◻ , _ | () , _
   ... | ◻ , _ | ◻ , _ | _ , R | ◻ , _ | ◻ , _ | _ , S = ◻ , [ (popᴹ ◻ *ᴹ) R │ S ]
   ... | ◻ , _ | ◻ , _ | _ , R | ◻ , _ | [ • x 〈 _ 〉 ᶜ ] , _ | _ , S = ◻ , [ (popᴹ ◻ *ᴹ) R │ S ]
   ... | ◻ , _ | ◻ , _ | _ , R | [ • x 〈 _ 〉 ᶜ ] , _ | [ • .x 〈 _ 〉 ᶜ ] , _ | [ • .x 〈 y 〉 ᶜ ] , S =
      ◻ , [ (popᴹ y *ᴹ) R │ S ]
   ... | ◻ , _ | [ (x •) ᵇ ] , _ | _ , R | ◻ , _ | ◻ , _ | _ , S = ◻ , [ (popᴹ ◻ *ᴹ) R │ S ]
   ... | ◻ , _ | [ (x •) ᵇ ] , _ | _ , R | ◻ , _ | [ • .x 〈 _ 〉 ᶜ ] , _ | _ , S = ◻ , [ (popᴹ ◻ *ᴹ) R │ S ]
   ... | ◻ , _ | [ (x •) ᵇ ] , _ | _ , R | [ • .x 〈 _ 〉 ᶜ ] , _ | [ • .x 〈 _ 〉 ᶜ ] , _ | [ • .x 〈 y 〉 ᶜ ] , S =
      ◻ , [ (popᴹ y *ᴹ) R │ S ]
   ... | [ (x •) ᵇ ] , _ | [ .x • ᵇ ] , _ | _ , R | ◻ , _ | ◻ , _ | _ , S = ◻ , [ (popᴹ ◻ *ᴹ) R │ S ]
   ... | [ (x •) ᵇ ] , _ | [ .x • ᵇ ] , _ | _ , R | ◻ , _ | [ • .x 〈 _ 〉 ᶜ ] , _ | _ , S = ◻ , [ (popᴹ ◻ *ᴹ) R │ S ]
   ... | [ (x •) ᵇ ] , _ | [ (.x •) ᵇ ] , _ | _ , R | [ • .x 〈 _ 〉 ᶜ ] , _ | [ • .x 〈 _ 〉 ᶜ ] , _ | [ • .x 〈 y 〉 ᶜ ] , S =
      [ τ ᶜ ] , [ (popᴹ y *ᴹ) R │ S ]

   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†)
      with step E P | step E P′ | stepᴹ E P† | step F Q | step F Q′ | stepᴹ F Q†
   ... | [ _ ] , _ | ◻ , _ | () , _ | _ | _ | _
   ... | _ | _ | _ | [ _ ] , _ | ◻ , _ | () , _
   ... | ◻ , _ | ◻ , _ | _ , R | ◻ , _ | ◻ , _ | _ , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ ◻ *ᴹ) R) │ S ] ]
   ... | ◻ , _ | ◻ , _ | _ , R | ◻ , _ | [ • ._ ﹙ _ ﹚ ᵇ ] , _ | _ , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ ◻ *ᴹ) R) │ S ] ]
   ... | ◻ , _ | ◻ , _ | _ , R | [ • x ﹙ _ ﹚ ᵇ ] , _ | [ • .x ﹙ _ ﹚ ᵇ ] , _ | [ • .x ﹙ y ﹚ ᵇ ] , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ y *ᴹ) R) │ S ] ]
   ... | ◻ , _ | [ x • ᵇ ] , _ | _ , R | ◻ , _ | ◻ , _ | _ , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ ◻ *ᴹ) R) │ S ] ]
   ... | ◻ , _ | [ x • ᵇ ] , _ | _ , R | ◻ , _ | [ • .x ﹙ _ ﹚ ᵇ ] , _ | _ , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ ◻ *ᴹ) R) │ S ] ]
   ... | ◻ , _ | [ x • ᵇ ] , _ | _ , R | [ • .x ﹙ _ ﹚ ᵇ ] , _ | [ • .x ﹙ _ ﹚ ᵇ ] , _ | [ • .x ﹙ y ﹚ ᵇ ] , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ y *ᴹ) R) │ S ] ]
   ... | [ x • ᵇ ] , _ | [ .x • ᵇ ] , _ | _ , R | ◻ , _ | ◻ , _ | _ , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ ◻ *ᴹ) R) │ S ] ]
   ... | [ x • ᵇ ] , _ | [ .x • ᵇ ] , _ | _ , R | ◻ , _ | [ • .x ﹙ _ ﹚ ᵇ ] , _ | _ , S =
      ◻ , [ ν [ id-elimᴹ ((replᴹ ◻ *ᴹ) R) │ S ] ]
   ... | [ x • ᵇ ] , _ | [ .x • ᵇ ] , _ | _ , R | [ • .x ﹙ _ ﹚ ᵇ ] , _ | [ • .x ﹙ _ ﹚ ᵇ ] , _ | [ • .x ﹙ y ﹚ ᵇ ] , S =
      [ τ ᶜ ] , [ ν [ id-elimᴹ ((replᴹ y *ᴹ) R) │ S ] ]

   step⁻ᴹ (ν•_ {x = x} E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ◻ , _ | ◻ , _ | ◻ , R† = ◻ , R†
   ... | ◻ , _ | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | ◻ , R† = ◻ , R†
   ... | ◻ , _ | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , _ | ◻ , R† = ◻ , R†
   ... | [ _ ] , _ | ◻ , _ | () , R†
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | _ , R† = [ • x ﹙ ◻ ﹚ ᵇ ] , R†
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , _ | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | [ • ._ 〈 () 〉 ᶜ ] , R†
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , _ | _ , R† = [ • x ﹙ ◻ ﹚ ᵇ ] , R†
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , _ | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , _ | _ , R† =
      [ • x ﹙ [ ᴺ.zero ] ﹚ ᵇ ] , R†

   step⁻ᴹ {a = x • ᵇ} (νᵇ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ◻ , _ | ◻ , _ | ◻ , R† = ◻ , [ ν (ᴹ swap *ᴹ) R† ]
   ... | ◻ , _ | [ ._ • ᵇ ] , _ | ◻ , R† = ◻ , [ ν (ᴹ swap *ᴹ) R† ]
   ... | [ _ ] , _ | ◻ , _ | () , _
   ... | [ ._ • ᵇ ] , _ | [ ._ • ᵇ ] , _ | _ , R† = [ x • ᵇ ] , [ ν (ᴹ swap *ᴹ) R† ]

   step⁻ᴹ {a = (• x) ᵇ} (νᵇ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ◻ , _ | ◻ , _ | ◻ , R† = ◻ , [ ν (ᴹ swap *ᴹ) R† ]
   ... | ◻ , _ | [ • ._ ﹙ ◻ ﹚ ᵇ ] , _ | ◻ , R† = ◻ , [ ν (ᴹ swap *ᴹ) R† ]
   ... | ◻ , _ | [ • ._ ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , _ | ◻ , R† = ◻ , [ ν (ᴹ swap *ᴹ) R† ]
   ... | [ _ ] , _ | ◻ , _ | () , _
   ... | [ • ._ ﹙ ◻ ﹚ ᵇ ] , _ | [ • ._ ﹙ ◻ ﹚ ᵇ ] , _ | _ , R† = [ • x ﹙ ◻ ﹚ ᵇ ] , [ ν (ᴹ swap *ᴹ) R† ]
   ... | [ • ._ ﹙ ◻ ﹚ ᵇ ] , _ | [ • ._ ﹙ [ ._ ] ﹚ ᵇ ] , _ | _ , R† = [ • x ﹙ ◻ ﹚ ᵇ ] , [ ν (ᴹ swap *ᴹ) R† ]
   ... | [ • ._ ﹙ [ ._ ] ﹚ ᵇ ] , _ | [ • ._ ﹙ ◻ ﹚ ᵇ ] , _ | [ • ._ ﹙ () ﹚ ᵇ ] , _
   ... | [ • ._ ﹙ [ ._ ] ﹚ ᵇ ] , _ | [ • ._ ﹙ [ ._ ] ﹚ ᵇ ] , _ | _ , R† =
      [ • x ﹙ [ ᴺ.zero ] ﹚ ᵇ ] , [ ν (ᴹ swap *ᴹ) R† ]

   step⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ◻ , _ | ◻ , _ | ◻ , R† = ◻ , [ ν R† ]
   ... | ◻ , _ | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | ◻ , R† = ◻ , [ ν R† ]
   ... | ◻ , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | ◻ , R† = ◻ , [ ν R† ]
   ... | [ _ ] , _ | ◻ , _ | () , R†
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | _ , R† = [ • x 〈 ◻ 〉 ᶜ ] , [ ν R† ]
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | _ , R† = [ • x 〈 ◻ 〉 ᶜ ] , [ ν R† ]
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | [ • ._ 〈 () 〉 ᶜ ] , _
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | _ , R† = [ • x 〈 [ y ] 〉 ᶜ ] , [ ν R† ]

   step⁻ᴹ {a = τ ᶜ} (νᶜ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ◻ , _ | ◻ , _ | ◻ , R† = ◻ , [ ν R† ]
   ... | ◻ , _ | [ τ ᶜ ] , _ | ◻ , R† = ◻ , [ ν R† ]
   ... | [ _ ] , _ | ◻ , _ | () , R†
   ... | [ τ ᶜ ] , _ | [ τ ᶜ ] , _ | [ τ ᶜ ] , R† = [ τ ᶜ ] , [ ν R† ]

   step⁻ᴹ (! E) (! P) = stepᴹ E [ P │ [ ! P ] ]

   action : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ P → ↓ a
   action E = π₁ ∘ᶠ step E

   actionᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓ P₀} → P ≤ P′ → action E P ≤ action E P′
   actionᴹ E = π₁ ∘ᶠ stepᴹ E

   -- Called 'fwd' in the paper.
   tgt : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ P → ↓ R
   tgt E = π₂ ∘ᶠ step E

   tgtᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓ P₀} → P ≤ P′ → tgt E P ≤ tgt E P′
   tgtᴹ E = π₂ ∘ᶠ stepᴹ E

   -- unstep reflects ◻.
   unstep : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓ ᵀ.out E → ↓ P
   unstep-◻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓⁻ a → ↓⁻ P
   unstep⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓ a → ↓⁻ P′ → ↓⁻ P

   unstep E (a , [ P ]) = [ unstep⁻ E a P ]
   unstep E ([ a ] , ◻) = [ unstep-◻ E a ]
   unstep _ (◻ , ◻) = ◻

   -- Variant which slices with a ◻ process and a non-◻ action.
   unstep-◻ (x •∙ P) (.x • ᵇ) = x •∙ ◻
   unstep-◻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ (E ➕₁ Q) a = [ unstep-◻ E a ] ➕ ◻
   unstep-◻ (E ᵇ│ Q) a = [ unstep-◻ E a ] │ ◻
   unstep-◻ (E ᶜ│ Q) a = [ unstep-◻ E a ] │ ◻
   unstep-◻ (P │ᵇ E) a = ◻ │ [ unstep-◻ E a ]
   unstep-◻ (P │ᶜ E) a = ◻ │ [ unstep-◻ E a ]
   unstep-◻ (E │• F) (τ ᶜ) = [ unstep-◻ E (_ • ᵇ) ] │ [ unstep-◻ F (• _ 〈 ◻ 〉 ᶜ) ]
   unstep-◻ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ E (_ • ᵇ) ] │ [ unstep-◻ F (• _ ﹙ ◻ ﹚ ᵇ) ]
   unstep-◻ (ν• E) (• x ﹙ ◻ ﹚ ᵇ) = ν [ unstep-◻ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) ]
   unstep-◻ (ν• E) (• x ﹙ [ .ᴺ.zero ] ﹚ ᵇ) = ν [ unstep-◻ E (• ᴺ.suc x 〈 zero 〉 ᶜ) ]
   unstep-◻ {a = x • ᵇ} (νᵇ E) (.x • ᵇ) = ν [ unstep-◻ E (ᴺ.suc x • ᵇ) ]
   unstep-◻ {a = (• x) ᵇ} (νᵇ E) (• .x ﹙ ◻ ﹚ ᵇ) = ν [ unstep-◻ E (• ᴺ.suc x ﹙ ◻ ﹚ ᵇ) ]
   unstep-◻ {a = (• x) ᵇ} (νᵇ E) (• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ) = ν [ unstep-◻ E (• ᴺ.suc x ﹙ zero ﹚ ᵇ) ]
   unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• .x 〈 ◻ 〉 ᶜ) = ν [ unstep-◻ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) ]
   unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• .x 〈 [ .y ] 〉 ᶜ) = ν [ unstep-◻ E (• ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ) ]
   unstep-◻ {a = τ ᶜ} (νᶜ E) (τ ᶜ) = ν [ unstep-◻ E (τ ᶜ) ]
   unstep-◻ (! E) a with unstep-◻ E a
   ... | P │ ◻ = ! P
   ... | P │ [ P′ ] = ! P ⊔⁻ P′

   -- Slice with a non-◻ process.
   unstep⁻ (x •∙ _) _ R = x •∙ [ R ]
   unstep⁻ (• x 〈 _ 〉∙ ._) ◻ R = • x 〈 ◻ 〉∙ [ R ]
   unstep⁻ (• x 〈 _ 〉∙ ._) [ • .x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ (E ➕₁ _) a R = [ unstep⁻ E a R ] ➕ ◻
   unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) = unstep E (a , R) │ π₂ (unren ᴿ.push Q S)
   unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) = unstep E (a , R) │ S
   unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) = π₂ (unren ᴿ.push P R) │ unstep E (a , S)
   unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) = R │ unstep E (a , S)
   unstep⁻ (_│•_ {R = P′} {x = x} {y} E F) ◻ (R │ S) with (π₁ (unren (ᴿ.pop y) P′ R)) ᴺ.zero
   ... | ◻ = unstep E (◻ , π₂ (unren (ᴿ.pop y) P′ R)) │ unstep F (◻ , S)
   ... | [ .y ] = unstep E (◻ , π₂ (unren (ᴿ.pop y) P′ R)) │ unstep F ([ • x 〈 [ y ] 〉 ᶜ ] , S)
   unstep⁻ (_│•_ {x = x} {y} E F) [ τ ᶜ ] (R │ S) =
      let pop-y , R′ = unren (ᴿ.pop y) (ᵀ.tgt E) R in
      unstep E ([ x • ᵇ ] , R′) │ unstep F ([ • x 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)
   unstep⁻ (E │ᵥ F) ◻ (ν ◻) = unstep E (◻ , ◻) │ unstep F (◻ , ◻)
   unstep⁻ (E │ᵥ F) [ τ ᶜ ] (ν ◻) = [ unstep-◻ E (_ • ᵇ) ] │ [ unstep-◻ F (• _ ﹙ ◻ ﹚ ᵇ) ]
   unstep⁻ (E │ᵥ F) ◻ (ν [ R │ S ]) with (π₁ (unren idᶠ (ᵀ.tgt E) (id-intro R))) ᴺ.zero
   ... | ◻ = unstep E ([ _ • ᵇ ] , R) │ unstep F (◻ , S)
   ... | [ .ᴺ.zero ] = unstep E (◻ , R) │ unstep F ([ • _ ﹙ zero ﹚ ᵇ ] , S)
   unstep⁻ (E │ᵥ F) [ τ ᶜ ] (ν [ R │ S ]) =
      let repl , _ = unren idᶠ (ᵀ.tgt E) (id-intro R) in
      unstep E ([ _ • ᵇ ] , R) │ unstep F ([ • _ ﹙ repl ̃ zero ﹚ ᵇ ] , S)
   unstep⁻ (ν• E) ◻ R = ν [ unstep⁻ E ◻ R ]
   unstep⁻ (ν• E) [ • x ﹙ ◻ ﹚ ᵇ ] R = ν [ unstep⁻ E [ • ᴺ.suc x 〈 ◻ 〉 ᶜ ] R ]
   unstep⁻ (ν• E) [ • x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] R = ν [ unstep⁻ E [ • ᴺ.suc x 〈 zero 〉 ᶜ ] R ]
   unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) ◻ (ν R) = ν unstep E (◻ , π₂ (unren ᴿ.swap P′ R))
   unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) [ .x • ᵇ ] (ν R) = ν unstep E ([ ᴺ.suc x • ᵇ ] , π₂ (unren ᴿ.swap P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) ◻ (ν R) = ν unstep E (◻ , π₂ (unren ᴿ.swap P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) [ • .x ﹙ ◻ ﹚ ᵇ ] (ν R) =
      ν unstep E ([ • ᴺ.suc x ﹙ ◻ ﹚ ᵇ ] , π₂ (unren ᴿ.swap P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] (ν R) =
      ν unstep E ([ • ᴺ.suc x ﹙ zero ﹚ ᵇ ] , π₂ (unren ᴿ.swap P′ R))
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) ◻ (ν R) = ν unstep E (◻ , R)
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) [ • .x 〈 ◻ 〉 ᶜ ] (ν R) = ν unstep E ([ (• ᴺ.suc x 〈 ◻ 〉) ᶜ ] , R)
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) [ • .x 〈 [ .y ] 〉 ᶜ ] (ν R) =
      ν unstep E ([ (• ᴺ.suc x 〈 [ ᴺ.suc y ] 〉) ᶜ ] , R)
   unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) ◻ (ν R) = ν unstep E (◻ , R)
   unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) [ τ ᶜ ] (ν R) = ν unstep E ([ τ ᶜ ] , R)
   unstep⁻ (! E) a R with unstep⁻ E a R
   ... | P │ ◻ = ! P
   ... | P │ [ P′ ] = ! P ⊔⁻ P′

   unstep-◻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓⁻ a} →
               a′ ≤⁻ a″ → unstep-◻ E a′ ≤⁻ unstep-◻ E a″
   unstep-◻ᴹ (x •∙ _) (.x • ᵇ) = x •∙ ◻
   unstep-◻ᴹ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ᴹ (E ➕₁ _) a = [ unstep-◻ᴹ E a ] ➕ ◻
   unstep-◻ᴹ (E ᵇ│ _) a = [ unstep-◻ᴹ E a ] │ ◻
   unstep-◻ᴹ (E ᶜ│ _) a = [ unstep-◻ᴹ E a ] │ ◻
   unstep-◻ᴹ (_ │ᵇ E) a = ◻ │ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (_ │ᶜ E) a = ◻ │ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (E │• F) (τ ᶜ) = [ unstep-◻ᴹ E (_ • ᵇ) ] │ [ unstep-◻ᴹ F (• _ 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) {• .x ﹙ ◻ ﹚ ᵇ} {• .x ﹙ ◻ ﹚ ᵇ} (• x ﹙ ◻ ﹚ ᵇ) = ν [ unstep-◻ᴹ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) {• .x ﹙ ◻ ﹚ ᵇ} {• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ} (• x ﹙ ◻ ﹚ ᵇ) = ν [ unstep-◻ᴹ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) {• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ} {• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ} (• x ﹙ [ .ᴺ.zero ] ﹚ ᵇ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x 〈 [ ᴺ.zero ] 〉 ᶜ) ]
   unstep-◻ᴹ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ᴹ E (_ • ᵇ) ] │ [ unstep-◻ᴹ F (• _ ﹙ ◻ ﹚ ᵇ) ]
   unstep-◻ᴹ {a = x • ᵇ} (νᵇ E) (._ • ᵇ) = ν [ unstep-◻ᴹ E (ᴺ.suc x • ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) {• .x ﹙ ◻ ﹚ ᵇ} {• .x ﹙ ◻ ﹚ ᵇ} (• .x ﹙ ◻ ﹚ ᵇ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x ﹙ ◻ ﹚ ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) {• .x ﹙ ◻ ﹚ ᵇ} {• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ} (• .x ﹙ ◻ ﹚ ᵇ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x ﹙ ◻ ﹚ ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) {• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ} {• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ} (• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x ﹙ [ ᴺ.zero ] ﹚ ᵇ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {• .x 〈 ◻ 〉 ᶜ} {• .x 〈 ◻ 〉 ᶜ} (• .x 〈 ◻ 〉 ᶜ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {• .x 〈 ◻ 〉 ᶜ} {• .x 〈 [ .y ] 〉 ᶜ} (• .x 〈 ◻ 〉 ᶜ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {• .x 〈 [ .y ] 〉 ᶜ} {• .x 〈 [ .y ] 〉 ᶜ} (• .x 〈 [ .y ] 〉 ᶜ) =
      ν [ unstep-◻ᴹ E (• ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ) ]
   unstep-◻ᴹ {a = τ ᶜ} (νᶜ E) (τ ᶜ) = ν [ unstep-◻ᴹ E (τ ᶜ) ]
   unstep-◻ᴹ (! E) {a′ = a′} {a″} a with unstep-◻ E a′ | unstep-◻ E a″ | unstep-◻ᴹ E a
   ... | _ │ ◻ | _ │ ◻ | P │ ◻ = ! P
   ... | _ │ ◻ | P │ [ ! P′ ] | P† │ _ = ! ≤-trans P† (P ⊔ʳ P′)
   ... | _ │ [ ! _ ] | _ │ ◻ | _ │ ()
   ... | _ │ [ ! _ ] | _ │ [ ! _ ] | P │ [ ! P′ ] = ! (P ⊔ᴹ P′)

   -- Auxiliary lemmas needed for monotonicity.
   unstep-◻-min : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻ a) (R : ↓ P′) →
                  [ unstep-◻ E a′ ] ≤ unstep E ([ a′ ] , R)
   unstep-◻-min⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻ a) (R : ↓⁻ P′) →
                   unstep-◻ E a′ ≤⁻ unstep⁻ E [ a′ ] R

   unstep-◻-min E a ◻ = [ ⁻ᴹ (unstep-◻ E a) ]
   unstep-◻-min E a [ R ] = [ unstep-◻-min⁻ E a R ]

   unstep-◻-min⁻ (x •∙ _) (.x • ᵇ) _ = x •∙ ◻
   unstep-◻-min⁻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) _ = • x 〈 ᴹ y 〉∙ ◻
   unstep-◻-min⁻ (E ➕₁ _) a P = [ unstep-◻-min⁻ E a P ] ➕ ◻
   unstep-◻-min⁻ (E ᵇ│ _) a (P │ Q) = unstep-◻-min E a P │ ◻
   unstep-◻-min⁻ (E ᶜ│ _) a (P │ Q) = unstep-◻-min E a P │ ◻
   unstep-◻-min⁻ (_ │ᵇ E) a (P │ Q) = ◻ │ unstep-◻-min E a Q
   unstep-◻-min⁻ (_ │ᶜ E) a (P │ Q) = ◻ │ unstep-◻-min E a Q
   unstep-◻-min⁻ (_│•_ {R = P′} {y = y} E F) (τ ᶜ) (P │ Q) with unren (ᴿ.pop y) P′ P
   ... | pop-y , R =
      unstep-◻-min E (_ • ᵇ) R │
      ≤-trans [ unstep-◻ᴹ F (• _ 〈 ◻ 〉 ᶜ) ] (unstep-◻-min F (• _ 〈 pop-y ᴺ.zero 〉 ᶜ) Q)
   unstep-◻-min⁻ (ν• E) (• x ﹙ ◻ ﹚ ᵇ) P = ν [ unstep-◻-min⁻ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) P ]
   unstep-◻-min⁻ (ν• E) (• x ﹙ [ .ᴺ.zero ] ﹚ ᵇ) P = ν [ unstep-◻-min⁻ E (• ᴺ.suc x 〈 zero 〉 ᶜ) P ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν ◻) = [ ⁻ᴹ (unstep-◻ E (_ • ᵇ)) ] │ [ ⁻ᴹ (unstep-◻ F (• _ ﹙ ◻ ﹚ ᵇ)) ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν [ P │ Q ]) =
      let repl , _ = unren idᶠ (ᵀ.tgt E) (id-intro P) in
      unstep-◻-min E (_ • ᵇ) P │ ≤-trans [ unstep-◻ᴹ F (• _ ﹙ ◻ ﹚ ᵇ) ] (unstep-◻-min F (• _ ﹙ repl ̃ zero ﹚ ᵇ) Q)
   unstep-◻-min⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) (.x • ᵇ) (ν P) =
      ν unstep-◻-min E (ᴺ.suc x • ᵇ) (π₂ (unren ᴿ.swap P′ P))
   unstep-◻-min⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) (• .x ﹙ ◻ ﹚ ᵇ) (ν P) =
      ν unstep-◻-min E (• ᴺ.suc x ﹙ ◻ ﹚ ᵇ) (π₂ (unren ᴿ.swap P′ P))
   unstep-◻-min⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) (• .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ) (ν P) =
      ν unstep-◻-min E (• ᴺ.suc x ﹙ zero ﹚ ᵇ) (π₂ (unren ᴿ.swap P′ P))
   unstep-◻-min⁻ {a = • .x 〈 y 〉 ᶜ} (νᶜ E) (• x 〈 ◻ 〉 ᶜ) (ν P) =
      ν unstep-◻-min E (• ᴺ.suc x 〈 ◻ 〉 ᶜ) P
   unstep-◻-min⁻ {a = • .x 〈 y 〉 ᶜ} (νᶜ E) (• x 〈 [ .y ] 〉 ᶜ) (ν P) =
      ν unstep-◻-min E (• ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ) P
   unstep-◻-min⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) (τ ᶜ) (ν P) = ν unstep-◻-min E (τ ᶜ) P
   unstep-◻-min⁻ (! E) a R with unstep-◻ E a | unstep⁻ E [ a ] R | unstep-◻-min⁻ E a R
   ... | _ │ ◻ | _ │ ◻ | P │ ◻ = ! P
   ... | _ │ ◻ | P │ [ ! P′ ] | P† │ _ = ! ≤-trans P† (P ⊔ʳ P′)
   ... | _ │ [ ! _ ] | _ │ [ ! _ ] | P │ [ ! P′ ] = ! (P ⊔ᴹ P′)

   unstepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {aR a′R′ : ↓ ᵀ.out E} →
             aR ≤ a′R′ → unstep E aR ≤ unstep E a′R′
   unstep⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓ a} {R R′ : ↓⁻ P′} →
              a′ ≤ a″ → R ≤⁻ R′ → unstep⁻ E a′ R ≤⁻ unstep⁻ E a″ R′

   unstepᴹ E (a , [ R ]) = [ unstep⁻ᴹ E a R ]
   unstepᴹ E {[ _ ] , ◻} {[ _ ] , ◻} ([ a ] , ◻) = [ unstep-◻ᴹ E a ]
   unstepᴹ E {[ _ ] , ◻} {[ _ ] , [ R ]} ([ a ] , ◻) = [ ≤⁻-trans (unstep-◻ᴹ E a) (unstep-◻-min⁻ E _ R) ]
   unstepᴹ E {◻ , ◻} (◻ , ◻) = ◻

   unstep⁻ᴹ (x •∙ _) {a″ = ◻} ◻ R = x •∙ [ R ]
   unstep⁻ᴹ (x •∙ _) {a″ = [ .x • ᵇ ]} ◻ R = x •∙ [ R ]
   unstep⁻ᴹ (x •∙ _) {a″ = [ .x • ᵇ ]} [ .x • ᵇ ] R = x •∙ [ R ]
   unstep⁻ᴹ (• x 〈 _ 〉∙ _) {a″ = ◻} ◻ R = • x 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• x 〈 _ 〉∙ _) {a″ = [ • .x 〈 _ 〉 ᶜ ]} ◻ R = • x 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• x 〈 _ 〉∙ _) {a″ = [ • .x 〈 _ 〉 ᶜ ]} [ • .x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ᴹ (E ➕₁ Q) a R = [ unstep⁻ᴹ E a R ] ➕ ◻
   unstep⁻ᴹ (E ᵇ│ Q) a′ (R │ S) = unstepᴹ E (a′ , R) │ π₂ (unrenᴹ ᴿ.push Q S)
   unstep⁻ᴹ (E ᶜ│ Q) a′ (R │ S) = unstepᴹ E (a′ , R) │ S
   unstep⁻ᴹ (P │ᵇ E) a′ (R │ S) = π₂ (unrenᴹ ᴿ.push P R) │ unstepᴹ E (a′ , S)
   unstep⁻ᴹ (P │ᶜ E) a′ (R │ S) = R │ unstepᴹ E (a′ , S)
   unstep⁻ᴹ (_│•_ {x = x} {y} E F) {a″ = ◻} {R = R′ │ _} {R″ │ _} ◻ (R │ S)
      with π₁ (unren (ᴿ.pop y) (ᵀ.tgt E) R′) ᴺ.zero | π₁ (unren (ᴿ.pop y) (ᵀ.tgt E) R″) ᴺ.zero |
           π₁ (unrenᴹ (ᴿ.pop y) (ᵀ.tgt E) R) ᴺ.zero
   ... | ◻ | ◻ | _ = unstepᴹ E (◻ , π₂ (unrenᴹ (ᴿ.pop y) (ᵀ.tgt E) R)) │ unstepᴹ F (◻ , S)
   ... | ◻ | [ .y ] | _ = unstepᴹ E (◻ , π₂ (unrenᴹ (ᴿ.pop y) (ᵀ.tgt E) R)) │ unstepᴹ F (◻ , S)
   ... | [ .y ] | ◻ | ()
   ... | [ .y ] | [ .y ] | _ =
      unstepᴹ E (◻ , π₂ (unrenᴹ (ᴿ.pop y) (ᵀ.tgt E) R)) │ unstepᴹ F ([ • x 〈 [ y ] 〉 ᶜ ] , S)
   unstep⁻ᴹ (_│•_ {R = P′} {x = x} {y} E F) {a″ = [ τ ᶜ ]} {R = R′ │ _} {R″ │ _} ◻ (R │ S)
      with π₁ (unren (ᴿ.pop y) P′ R′) ᴺ.zero | π₁ (unren (ᴿ.pop y) P′ R″) ᴺ.zero |  π₁ (unrenᴹ (ᴿ.pop y) P′ R) ᴺ.zero
   ... | ◻ | _ | _ = unstepᴹ E (◻ , π₂ (unrenᴹ (ᴿ.pop y) P′ R)) │ unstepᴹ F (◻ , S)
   ... | [ .y ] | ◻ | ()
   ... | [ .y ] | [ .y ] | _ =
      unstepᴹ E (◻ , π₂ (unrenᴹ (ᴿ.pop y) P′ R)) │ unstepᴹ F ([ • x 〈 [ y ] 〉 ᶜ ] , S)
   unstep⁻ᴹ (_│•_ {R = P′} {y = y} E F) {a″ = [ τ ᶜ ]} [ τ ᶜ ] (R │ S) =
      let pop-y , R′ = unrenᴹ (ᴿ.pop y) P′ R in
      unstepᴹ E ([ _ • ᵇ ] , R′) │ unstepᴹ F ([ • _ 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)
   unstep⁻ᴹ (ν• E) {a″ = ◻} ◻ R = ν [ unstep⁻ᴹ E ◻ R ]
   unstep⁻ᴹ (ν• E) {a″ = [ • x ﹙ ◻ ﹚ ᵇ ]} ◻ R = ν [ unstep⁻ᴹ E ◻ R ]
   unstep⁻ᴹ (ν• E) {a″ = [ • ._ ﹙ [ .ᴺ.zero ] ﹚ ᵇ ]} ◻ R = ν [ unstep⁻ᴹ E ◻ R ]
   unstep⁻ᴹ (ν• E) {a″ = [ • x ﹙ ◻ ﹚ ᵇ ]} [ • .x ﹙ ◻ ﹚ ᵇ ] R = ν [ unstep⁻ᴹ E [ • ᴺ.suc x 〈 ◻ 〉 ᶜ ] R ]
   unstep⁻ᴹ (ν• E) {a″ = [ • x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ]} [ • .x ﹙ ◻ ﹚ ᵇ ] R = ν [ unstep⁻ᴹ E [ • ᴺ.suc _ 〈 ◻ 〉 ᶜ ] R ]
   unstep⁻ᴹ (ν• E) [ • x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] R = ν [ unstep⁻ᴹ E [ • ᴺ.suc _ 〈 [ ᴺ.zero ] 〉 ᶜ ] R ]
   unstep⁻ᴹ (E │ᵥ F) {a″ = ◻} {R′ = ν ◻} ◻ (ν ◻) = ◻ │ ◻
   unstep⁻ᴹ (E │ᵥ F) {a″ = [ τ ᶜ ]} {R′ = ν ◻} ◻ (ν ◻) = ◻ │ ◻
   unstep⁻ᴹ (E │ᵥ F) {a″ = [ τ ᶜ ]} {R′ = ν ◻} [ τ ᶜ ] (ν ◻) =
      [ ⁻ᴹ (unstep-◻ E (_ • ᵇ)) ] │ [ ⁻ᴹ (unstep-◻ F (• _ ﹙ ◻ ﹚ ᵇ)) ]
   unstep⁻ᴹ (E │ᵥ F) {a″ = ◻} {R′ = ν [ P │ Q ]} ◻ (ν ◻)
      with π₁ (unren idᶠ (ᵀ.tgt E) (id-intro P)) ᴺ.zero
   ... | ◻ = ◻ │ ◻
   ... | [ .ᴺ.zero ] = ◻ │ ◻
   unstep⁻ᴹ (E │ᵥ F) {a″ = [ τ ᶜ ]} {R′ = ν [ P │ Q ]} ◻ (ν ◻) = ◻ │ ◻
   unstep⁻ᴹ (E │ᵥ F) {a″ = [ τ ᶜ ]} {R′ = ν [ P │ Q ]} [ τ ᶜ ] (ν ◻) =
      unstep-◻-min E (_ • ᵇ) P │ ≤-trans (unstep-◻-min F (• _ ﹙ ◻ ﹚ ᵇ) Q) (unstepᴹ F ([ • _ ﹙ ◻ ﹚ ᵇ ] , ᴹ Q))
   unstep⁻ᴹ (E │ᵥ F) {a″ = ◻} {R′ = ν [ _ │ _ ]} ◻ (ν [ R │ S ]) = {!!}
--      unstepᴹ E (◻ , R) │ unstepᴹ F (◻ , S)
   unstep⁻ᴹ (E │ᵥ F) {a″ = [ τ ᶜ ]} {R′ = ν [ _ │ _ ]} ◻ (ν [ R │ S ]) =
      {!!} -- unstepᴹ E (◻ , R) │ unstepᴹ F (◻ , S)
   unstep⁻ᴹ (E │ᵥ F) {a″ = [ τ ᶜ ]} {R′ = ν [ _ │ _ ]} [ τ ᶜ ] (ν [ R │ S ]) =
      unstepᴹ E ([ _ • ᵇ ] , R) │ unstepᴹ F ([ • _ ﹙ π₁ (unrenᴹ idᶠ (ᵀ.tgt E) (id-introᴹ R)) ᴺ.zero ﹚ ᵇ ] , S)
   unstep⁻ᴹ {a = x • ᵇ} (νᵇ_ {R = P′} E) {a″ = ◻} ◻ (ν R) = ν unstepᴹ E (◻ , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ x • ᵇ ]} ◻ (ν R) = ν unstepᴹ E (◻ , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ x • ᵇ ]} [ .x • ᵇ ] (ν R) =
      ν unstepᴹ E ([ ᴺ.suc x • ᵇ ] , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) {a″ = ◻} ◻ (ν R) = ν unstepᴹ E (◻ , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ • x ﹙ ◻ ﹚ ᵇ ]} ◻ (ν R) = ν unstepᴹ E (◻ , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ • x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ]} ◻ (ν R) = ν unstepᴹ E (◻ , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ • x ﹙ ◻ ﹚ ᵇ ]} [ • .x ﹙ ◻ ﹚ ᵇ ] (ν R) =
      ν unstepᴹ E ([ • ᴺ.suc x ﹙ ◻ ﹚ ᵇ ] , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ • x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ]} [ • .x ﹙ ◻ ﹚ ᵇ ] (ν R) =
      ν unstepᴹ E ([ • ᴺ.suc x ﹙ ◻ ﹚ ᵇ ] , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ (νᵇ_ {R = P′} E) {a″ = [ • x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ]} [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] (ν R) =
      ν unstepᴹ E ([ • ᴺ.suc x ﹙ [ ᴺ.zero ] ﹚ ᵇ ] , π₂ (unrenᴹ ᴿ.swap P′ R))
   unstep⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {a″ = ◻} ◻ (ν R) = ν unstepᴹ E (◻ , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ • x 〈 ◻ 〉 ᶜ ]} ◻ (ν R) = ν unstepᴹ E (◻ , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ • x 〈 [ y ] 〉 ᶜ ]} ◻ (ν R) = ν unstepᴹ E (◻ , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ • x 〈 ◻ 〉 ᶜ ]} [ • .x 〈 ◻ 〉 ᶜ ] (ν R) =
      ν unstepᴹ E ([ • ᴺ.suc x 〈 ◻ 〉 ᶜ ] , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ • x 〈 [ y ] 〉 ᶜ ]} [ • .x 〈 ◻ 〉 ᶜ ] (ν R) =
      ν unstepᴹ E ([ • ᴺ.suc x 〈 ◻ 〉 ᶜ ] , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ • x 〈 [ y ] 〉 ᶜ ]} [ • .x 〈 [ .y ] 〉 ᶜ ] (ν R) =
      ν unstepᴹ E ([ • ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ ] , R)
   unstep⁻ᴹ {a = τ ᶜ} (νᶜ E) {a″ = ◻} ◻ (ν R) = ν unstepᴹ E (◻ , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ τ ᶜ ]} ◻ (ν R) = ν unstepᴹ E (◻ , R)
   unstep⁻ᴹ (νᶜ E) {a″ = [ τ ᶜ ]} [ τ ᶜ ] (ν R) = ν unstepᴹ E ([ τ ᶜ ] , R)
   unstep⁻ᴹ (! E) {a′} {a″} {R′} {R″} a R with unstep⁻ E a′ R′ | unstep⁻ E a″ R″ | unstep⁻ᴹ E a R
   ... | _ │ ◻ | _ │ ◻ | P │ ◻ = ! P
   ... | _ │ ◻ | P │ [ ! P′ ] | P† │ _ = ! ≤-trans P† (P ⊔ʳ P′)
   ... | _ │ [ ! _ ] | _ │ [ ! _ ] | P │ [ ! P′ ] = ! (P ⊔ᴹ P′)

   -- Called 'bwd' in the paper.
   src : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ R → ↓ P
   src E R = unstep E (◻ , R)

   srcᴹ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) {R R′ : ↓ R} → R ≤ R′ → src E R ≤ src E R′
   srcᴹ E R = unstepᴹ E (◻ , R)
