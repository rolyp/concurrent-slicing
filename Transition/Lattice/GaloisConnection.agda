module Transition.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra
   open import Ext.Algebra.Structures

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Lattice as ᴬ̃ using (top; ↓ᵇ⁻_; ↓ᶜ⁻_);
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ⁻_; open ᴬ̃._≤ᶜ⁻_
   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Proc using (Proc)
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (_†; _†ᴹ; _*ᴹ) renaming (_* to _*̃)
   open import Proc.Ren.Lattice.GaloisConnection using (id≤ren∘unren; unren∘ren≤id)
   import Name as ᴺ
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Ren as ᴿ using (push; pop; swap; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (pop-top)
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Lattice as ᵀ̃
      using (source; sourceᴹ; source⁻; source⁻ᴹ; out; outᴹ; action; actionᴹ);
      open ᵀ̃.↓_; open ᵀ̃.↓⁻_; open ᵀ̃._≤_; open ᵀ̃._≤⁻_

   step : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ P → ↓ E
   step⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻ P → ↓ E

   step E [ P ] = step⁻ E P
   step E ◻ = ◻

   step⁻ (_ •∙ _) (x •∙ P) = [ x •∙ P ]
   step⁻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ P) = [ • x 〈 y 〉∙ P ]
   step⁻ (E ➕₁ _) (P ➕ Q) = [ step E P ➕₁ Q ]
   step⁻ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = [ step E P ᵇ│ Q ]
   step⁻ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = [ step E P ᶜ│ Q ]
   step⁻ {a = _ ᵇ} (_ │ᵇ E) (P │ Q) = [ P │ᵇ step E Q ]
   step⁻ {a = _ ᶜ} (_ │ᶜ E) (P │ Q) = [ P │ᶜ step E Q ]
   step⁻ (E │• F) (P │ Q) with action (step E P) | action (step F Q)
   ... | [ [ x ] • ᵇ ] | [ • [ .x ] 〈 y 〉 ᶜ ] = [ step E P │• step F Q ]
   ... | _ | _ = ◻
   step⁻ (E │ᵥ F) (P │ Q) with action (step E P) | action (step F Q)
   ... | [ [ x ] • ᵇ ] | [ (• [ .x ]) ᵇ ] = [ step E P │ᵥ step F Q ]
   ... | _ | _ = ◻
   step⁻ (ν• E) (ν P) with action (step E P)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ ν• (step E P) ]
   ... | _ = ◻
   step⁻ {a = _ • ᵇ} (νᵇ E) (ν P) with action (step E P)
   ... | [ [ ._ ] • ᵇ ] = [ νᵇ (step E P) ]
   ... | _ = ◻
   step⁻ {a = (• _) ᵇ} (νᵇ E) (ν P) with action (step E P)
   ... | [ (• [ ._ ]) ᵇ ] = [ νᵇ (step E P) ]
   ... | _ = ◻
   step⁻ {a = • _ 〈 _ 〉 ᶜ} (νᶜ E) (ν P) with action (step E P)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ νᶜ (step E P) ]
   ... | _ = ◻
   step⁻ {a = τ ᶜ} (νᶜ E) (ν P) with action (step E P)
   ... | [ τ ᶜ ] = [ νᶜ (step E P) ]
   ... | _ = ◻
   step⁻ (! E) (! P) = [ ! (step E [ P │ [ ! P ] ]) ]

   stepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {R R′ : ↓ P} → R ≤ R′ → step E R ≤ step E R′
   step⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {R R′ : ↓⁻ P} → R ≤⁻ R′ → step⁻ E R ≤ step⁻ E R′

   stepᴹ E [ P ] = step⁻ᴹ E P
   stepᴹ E ◻ = ◻

   step⁻ᴹ (_ •∙ _) (x •∙ P) = [ x •∙ P ]
   step⁻ᴹ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ P) = [ • x 〈 y 〉∙ P ]
   step⁻ᴹ (E ➕₁ _) (P ➕ Q) = [ stepᴹ E P ➕₁ Q ]
   step⁻ᴹ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = [ stepᴹ E P ᵇ│ Q ]
   step⁻ᴹ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = [ stepᴹ E P ᶜ│ Q ]
   step⁻ᴹ {a = _ ᵇ} (_ │ᵇ E) (P │ Q) = [ P │ᵇ stepᴹ E Q ]
   step⁻ᴹ {a = _ ᶜ} (_ │ᶜ E) (P │ Q) = [ P │ᶜ stepᴹ E Q ]
   step⁻ᴹ (E │• F) {R = R │ S} {R′ │ S′} (P │ Q) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | .◻ | _ | ◻ = ◻
   ... | ._ | ._ | [ ◻ • ᵇ ] = ◻
   ... | [ [ x ] • ᵇ ] | [ [ .x ] • ᵇ ] | [ [ .x ] • ᵇ ]
      with action (step F S) | action (step F S′) | actionᴹ (stepᴹ F Q)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ .x ] 〈 _ 〉 ᶜ ] | [ • [ .x ] 〈 _ 〉 ᶜ ] | [ • [ .x ] 〈 _ 〉 ᶜ ] = [ stepᴹ E P │• stepᴹ F Q ]
   step⁻ᴹ (E │ᵥ F) {R = R │ S} {R′ │ S′} (P │ Q) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] | [ _ • ᵇ ] | [ ◻ • ᵇ ] = ◻
   ... | [ ([ x ] •) ᵇ ] | [ ([ .x ] •) ᵇ ] | [ ([ .x ] •) ᵇ ]
      with action (step F S) | action (step F S′) | actionᴹ (stepᴹ F Q)
   ... | ◻ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] | [ (• _) ᵇ ] | [ (• ◻) ᵇ ] = ◻
   ... | [ (• [ .x ]) ᵇ ] | [ (• [ .x ]) ᵇ ] | [ (• [ .x ]) ᵇ ] = [ stepᴹ E P │ᵥ stepᴹ F Q ]
   step⁻ᴹ (ν• E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ ν• (stepᴹ E P) ]
   step⁻ᴹ {a = (• x) ᵇ} (νᵇ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] | [ (• _) ᵇ ] | [ (• ◻) ᵇ ] = ◻
   ... | [ (• [ ._ ]) ᵇ ] | [ (• [ ._ ]) ᵇ ] | [ (• [ ._ ]) ᵇ ] = [ νᵇ (stepᴹ E P) ]
   step⁻ᴹ {a = x • ᵇ} (νᵇ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] | [ _ • ᵇ ] | [ ◻ • ᵇ ] = ◻
   ... | [ [ ._ ] • ᵇ ] | [ [ ._ ] • ᵇ ] | [ [ ._ ] • ᵇ ] = [ νᵇ (stepᴹ E P) ]
   step⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {R = ν R} {ν R′} (ν P)
      with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ νᶜ (stepᴹ E P) ]
   ... | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] | [ • () 〈 _ 〉 ᶜ ]
   step⁻ᴹ {a = τ ᶜ} (νᶜ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ τ ᶜ ] | [ τ ᶜ ] | [ τ ᶜ ] = [ νᶜ (stepᴹ E P) ]
   step⁻ᴹ (! E) (! P) = [ ! stepᴹ E [ P │ [ ! P ] ] ]

   -- unstep reflects ◻. The unstep-◻ variant slices with a ◻ process and a non-◻ action. The recursion case
   -- is simpler than in the paper, because we don't specify here the slice of the source process.
   unstep : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓ a → ↓ P′ → ↓ E
   unstep-◻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓⁻ a → ↓⁻ E
   unstep⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓ a → ↓⁻ P′ → ↓⁻ E

   unstep E a [ R ] = [ unstep⁻ E a R ]
   unstep E [ a ] ◻ = [ unstep-◻ E a ]
   unstep _ ◻ ◻ = ◻

   unstep-◻ (_ •∙ P) (x • ᵇ) = x •∙ ◻
   unstep-◻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ (E ➕₁ Q) a = [ unstep-◻ E a ] ➕₁ ◻
   unstep-◻ (E ᵇ│ Q) a = [ unstep-◻ E a ] ᵇ│ ◻
   unstep-◻ (E ᶜ│ Q) a = [ unstep-◻ E a ] ᶜ│ ◻
   unstep-◻ (P │ᵇ E) a = ◻ │ᵇ [ unstep-◻ E a ]
   unstep-◻ (P │ᶜ E) a = ◻ │ᶜ [ unstep-◻ E a ]
   unstep-◻ (E │• F) (τ ᶜ) = [ unstep-◻ E ([ _ ] • ᵇ) ] │• [ unstep-◻ F (• [ _ ] 〈 ◻ 〉 ᶜ) ]
   unstep-◻ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ F ((• [ _ ]) ᵇ) ]
   unstep-◻ (ν• E) ((• _) ᵇ) = ν• [ unstep-◻ E (• suc [ _ ] 〈 zero 〉 ᶜ) ]
   unstep-◻ {a = x • ᵇ} (νᵇ E) _ = νᵇ [ unstep-◻ E ([ (push *) x ] • ᵇ) ]
   unstep-◻ {a = (• x) ᵇ} (νᵇ E) _ = νᵇ [ unstep-◻ E ((• [ (push *) x ]) ᵇ) ]
   unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) _ = νᶜ [ unstep-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ) ]
   unstep-◻ {a = τ ᶜ} (νᶜ E) _ = νᶜ [ unstep-◻ E (τ ᶜ) ]
   unstep-◻ (! E) a = ! [ unstep-◻ E a ]

   unstep⁻ (_ •∙ _) ◻ R = ◻ •∙ [ R ]
   unstep⁻ (_ •∙ _) [ x • ᵇ ] R = x •∙ [ R ]
   unstep⁻ (• _ 〈 _ 〉∙ ._) ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ (• _ 〈 _ 〉∙ ._) [ • x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ (E ➕₁ _) a R = [ unstep⁻ E a R ] ➕₁ ◻
   unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) = unstep E a R ᵇ│ π₂ ((push †) Q S)
   unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) = unstep E a R ᶜ│ S
   unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) = π₂ ((push †) P R) │ᵇ unstep E a S
   unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) = R │ᶜ unstep E a S
   unstep⁻ (_│•_ {R = P′} {x = x} {y} E F) _ (R │ S) with (pop y †) P′ R
   ... | pop-y , R′ = unstep E [ [ _ ] • ᵇ ] R′ │• unstep F [ • [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ ] S
   unstep⁻ (E │ᵥ F) _ (ν ◻) = [ unstep-◻ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ F ((• [ _ ]) ᵇ) ]
   unstep⁻ (E │ᵥ F) _ (ν [ R │ S ]) = unstep E [ [ _ ] • ᵇ ] R │ᵥ unstep F [ (• [ _ ]) ᵇ ] S
   unstep⁻ (ν• E) _ R = ν• [ unstep⁻ E [ • suc [ _ ] 〈 zero 〉 ᶜ ] R ]
   unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstep E [ [ (push *) x ] • ᵇ ] (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstep E [ (• [ (push *) x ]) ᵇ ] (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstep E [ (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉) ᶜ ] R
   unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstep E [ τ ᶜ ] R
   unstep⁻ (! E) a R = ! [ unstep⁻ E a R ]

   unstep-◻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓⁻ a} →
               a′ ≤⁻ a″ → unstep-◻ E a′ ≤⁻ unstep-◻ E a″
   unstep-◻ᴹ (_ •∙ _) (x • ᵇ) = x •∙ ◻
   unstep-◻ᴹ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ᴹ (E ➕₁ _) a = [ unstep-◻ᴹ E a ] ➕₁ ◻
   unstep-◻ᴹ (E ᵇ│ _) a = [ unstep-◻ᴹ E a ] ᵇ│ ◻
   unstep-◻ᴹ (E ᶜ│ _) a = [ unstep-◻ᴹ E a ] ᶜ│ ◻
   unstep-◻ᴹ (_ │ᵇ E) a = ◻ │ᵇ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (_ │ᶜ E) a = ◻ │ᶜ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (E │• F) (τ ᶜ) = [ unstep-◻ᴹ E ([ _ ] • ᵇ) ] │• [ unstep-◻ᴹ F (• [ _ ] 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) ((• _) ᵇ) = ν• [ unstep-◻ᴹ E (• sucᴹ [ _ ] 〈 ᴹ zero 〉 ᶜ) ]
   unstep-◻ᴹ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ᴹ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ᴹ F ((• [ _ ]) ᵇ) ]
   unstep-◻ᴹ {a = x • ᵇ} (νᵇ E) (_ • ᵇ) = νᵇ [ unstep-◻ᴹ E ([ (ᴿ.push *) x ] • ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) ((• _) ᵇ) = νᵇ [ unstep-◻ᴹ E ((• [ (ᴿ.push *) x ]) ᵇ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• _ 〈 _ 〉 ᶜ) = νᶜ [ unstep-◻ᴹ E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ᴹ {a = τ ᶜ} (νᶜ E) (τ ᶜ) = νᶜ [ unstep-◻ᴹ E (τ ᶜ) ]
   unstep-◻ᴹ (! E) a = ! [ unstep-◻ᴹ E a ]

   -- Auxiliary lemmas needed for monotonicity.
   unstep-◻-min : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻ a) (R : ↓ P′) →
                  [ unstep-◻ E a′ ] ≤ unstep E [ a′ ] R
   unstep-◻-min⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻ a) (R : ↓⁻ P′) →
                   unstep-◻ E a′ ≤⁻ unstep⁻ E [ a′ ] R

   unstep-◻-min E a ◻ = [ ⁻ᴹ (unstep-◻ E a) ]
   unstep-◻-min E a [ R ] = [ unstep-◻-min⁻ E a R ]

   unstep-◻-min⁻ (_ •∙ _) (x • ᵇ) _ = ᴹ x •∙ ◻
   unstep-◻-min⁻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) _ = • ᴹ x 〈 ᴹ y 〉∙ ◻
   unstep-◻-min⁻ (E ➕₁ _) a P = [ unstep-◻-min⁻ E a P ] ➕₁ ◻
   unstep-◻-min⁻ (E ᵇ│ _) a (P │ Q) = unstep-◻-min E a P ᵇ│ ◻
   unstep-◻-min⁻ (E ᶜ│ _) a (P │ Q) = unstep-◻-min E a P ᶜ│ ◻
   unstep-◻-min⁻ (_ │ᵇ E) a (P │ Q) = ◻ │ᵇ unstep-◻-min E a Q
   unstep-◻-min⁻ (_ │ᶜ E) a (P │ Q) = ◻ │ᶜ unstep-◻-min E a Q
   unstep-◻-min⁻ (_│•_ {R = P′} {y = y} E F) (τ ᶜ) (P │ Q) with (ᴿ.pop y †) P′ P
   ... | pop-y , R =
      unstep-◻-min E ([ _ ] • ᵇ) R │•
      ≤-trans [ unstep-◻ᴹ F (• [ _ ] 〈 ◻ 〉 ᶜ) ] (unstep-◻-min F (• [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ) Q)
   unstep-◻-min⁻ (ν• E) ((• _) ᵇ) P = ν• [ unstep-◻-min⁻ E (• suc [ _ ] 〈 zero 〉 ᶜ) P ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν ◻) = [ ⁻ᴹ (unstep-◻ E ([ _ ] • ᵇ)) ] │ᵥ [ ⁻ᴹ (unstep-◻ F ((• [ _ ]) ᵇ)) ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν [ P │ Q ]) = unstep-◻-min E ([ _ ] • ᵇ) P │ᵥ unstep-◻-min F ((• [ _ ]) ᵇ) Q
   unstep-◻-min⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = νᵇ unstep-◻-min E ([ (push *) x ] • ᵇ) (π₂ ((swap †) P′ P))
   unstep-◻-min⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = νᵇ unstep-◻-min E ((• [ (push *) x ]) ᵇ) (π₂ ((swap †) P′ P))
   unstep-◻-min⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = νᶜ unstep-◻-min E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ) P
   unstep-◻-min⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = νᶜ unstep-◻-min E (τ ᶜ) P
   unstep-◻-min⁻ (! E) a R = ! [ unstep-◻-min⁻ E a R ]

   unstepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓ a} {R R′ : ↓ P′} →
                a′ ≤ a″ → R ≤ R′ → unstep E a′ R ≤ unstep E a″ R′
   unstep⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓ a} {R R′ : ↓⁻ P′} →
              a′ ≤ a″ → R ≤⁻ R′ → unstep⁻ E a′ R ≤⁻ unstep⁻ E a″ R′

   unstepᴹ E a [ R ] = [ unstep⁻ᴹ E a R ]
   unstepᴹ E {[ _ ]} {[ _ ]} {◻} {◻} [ a ] ◻ = [ unstep-◻ᴹ E a ]
   unstepᴹ E {[ _ ]} {[ _ ]} {◻} {[ R ]} [ a ] ◻ = [ ≤⁻-trans (unstep-◻ᴹ E a) (unstep-◻-min⁻ E _ R) ]
   unstepᴹ E {◻} ◻ ◻ = ◻

   unstep⁻ᴹ (_ •∙ _) {◻} {◻} ◻ R = ◻ •∙ [ R ]
   unstep⁻ᴹ (_ •∙ _) {◻} {[ _ • ᵇ ]} ◻ R = ◻ •∙ [ R ]
   unstep⁻ᴹ (_ •∙ _) {[ _ • ᵇ ]} {[ _ • ᵇ ]} [ u • ᵇ ] R = u •∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {◻} {◻} ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {◻} {[ • _ 〈 _ 〉 ᶜ ]} ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {[ • _ 〈 _ 〉 ᶜ ]} {[ • _ 〈 _ 〉 ᶜ ]} [ • x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ᴹ (E ➕₁ Q) a R = [ unstep⁻ᴹ E a R ] ➕₁ ◻
   unstep⁻ᴹ (E ᵇ│ Q) a′ (R │ S) = unstepᴹ E a′ R ᵇ│ π₂ ((push †ᴹ) Q S)
   unstep⁻ᴹ (E ᶜ│ Q) a′ (R │ S) = unstepᴹ E a′ R ᶜ│ S
   unstep⁻ᴹ (P │ᵇ E) a′ (R │ S) = π₂ ((ᴿ.push †ᴹ) P R) │ᵇ unstepᴹ E a′ S
   unstep⁻ᴹ (P │ᶜ E) a′ (R │ S) = R │ᶜ unstepᴹ E a′ S
   unstep⁻ᴹ (_│•_ {R = P″} {y = y} E F) {R = P │ _} {P′ │ _} a (R │ S) with (pop y †ᴹ) P″ R
   ... | pop-y , R′ = unstepᴹ E [ [ _ ] • ᵇ ] R′ │• unstepᴹ F [ • [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ ] S
   unstep⁻ᴹ (ν• E) _ R = ν• [ unstep⁻ᴹ E [ • sucᴹ [ _ ] 〈 ᴹ zero 〉 ᶜ ] R ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν ◻} _ (ν ◻) = [ ⁻ᴹ (unstep-◻ E ([ _ ] • ᵇ)) ] │ᵥ [ ⁻ᴹ (unstep-◻ F ((• _) ᵇ)) ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν [ P │ Q ]} _ (ν ◻) = unstep-◻-min E ([ _ ] • ᵇ) P │ᵥ unstep-◻-min F ((• _) ᵇ) Q
   unstep⁻ᴹ (E │ᵥ F) {R = ν [ _ │ _ ]} {ν [ _ │ _ ]} _ (ν [ R │ S ]) =
      unstepᴹ E [ [ _ ] • ᵇ ] R │ᵥ unstepᴹ F [ (• [ _ ]) ᵇ ] S
   unstep⁻ᴹ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstepᴹ E [ [ (push *) x ] • ᵇ ] (π₂ ((swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstepᴹ E [ (• [ (push *) x ]) ᵇ ] (π₂ ((swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstepᴹ E [ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] R
   unstep⁻ᴹ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstepᴹ E [ τ ᶜ ] R
   unstep⁻ᴹ (! E) a R = ! [ unstep⁻ᴹ E a R ]

   fwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ P → ↓ (a , R)
   fwd E = out ∘ᶠ step E

   fwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻ P → ↓ (a , R)
   fwd⁻ E = out ∘ᶠ step⁻ E

   fwdᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓ P₀} → P ≤ P′ → fwd E P ≤ fwd E P′
   fwdᴹ E = outᴹ ∘ᶠ stepᴹ E

   fwd⁻ᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓⁻ P₀} → P ≤⁻ P′ → fwd⁻ E P ≤ fwd⁻ E P′
   fwd⁻ᴹ E = outᴹ ∘ᶠ step⁻ᴹ E

   bwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ (a , R) → ↓ P
   bwd E (a , R) = source (unstep E a R)

   bwdᴹ : ∀ {Γ P} {a₀ : Action Γ} {R₀} (E : P —[ a₀ - _ ]→ R₀) {a a′ : ↓ a₀} {R R′ : ↓ R₀} →
          (a , R) ≤ (a′ , R′) → bwd E (a , R) ≤ bwd E (a′ , R′)
   bwdᴹ E (a , R) = sourceᴹ (unstepᴹ E a R)

   bwd-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻ a → ↓⁻ P
   bwd-◻ E a = source⁻ (unstep-◻ E a)

   bwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓ a → ↓⁻ R → ↓⁻ P
   bwd⁻ E a R = source⁻ (unstep⁻ E a R)

   bwd⁻ᴹ : ∀ {Γ P} {a₀ : Action Γ} {R₀} (E : P —[ a₀ - _ ]→ R₀) {a a′ : ↓ a₀} {R R′ : ↓⁻ R₀} →
          a ≤ a′ → R ≤⁻ R′ → bwd⁻ E a R ≤⁻ bwd⁻ E a′ R′
   bwd⁻ᴹ E a R = source⁻ᴹ (unstep⁻ᴹ E a R)

   id≤fwd∘bwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (aR : ↓ (a , R)) → aR ≤ (fwd E ∘ᶠ bwd E) aR
   id≤fwd⁻∘bwd-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓⁻ a) → [ a′ ] ≤ π₁ (fwd⁻ E (bwd-◻ E a′))
   id≤fwd⁻∘bwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓ a) (R′ : ↓⁻ R) → (a′ , [ R′ ]) ≤ fwd⁻ E (bwd⁻ E a′ R′)

   id≤fwd∘bwd E (a , [ R ]) = id≤fwd⁻∘bwd⁻ E a R
   id≤fwd∘bwd E ([ a ] , ◻) = id≤fwd⁻∘bwd-◻ E a , ◻
   id≤fwd∘bwd _ (◻ , ◻) = ◻ , ◻

   id≤fwd⁻∘bwd-◻ (_ •∙ _) (x • ᵇ) = [ ᴹ x • ᵇ ]
   id≤fwd⁻∘bwd-◻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = [ • ᴹ x 〈 ᴹ y 〉 ᶜ ]
   id≤fwd⁻∘bwd-◻ (E ➕₁ Q) a = id≤fwd⁻∘bwd-◻ E a
   id≤fwd⁻∘bwd-◻ (E ᵇ│ Q) (a ᵇ) = id≤fwd⁻∘bwd-◻ E (a ᵇ)
   id≤fwd⁻∘bwd-◻ (E ᶜ│ Q) (a ᶜ) = id≤fwd⁻∘bwd-◻ E (a ᶜ)
   id≤fwd⁻∘bwd-◻ (P │ᵇ E) (a ᵇ) = id≤fwd⁻∘bwd-◻ E (a ᵇ)
   id≤fwd⁻∘bwd-◻ (P │ᶜ E) (a ᶜ) = id≤fwd⁻∘bwd-◻ E (a ᶜ)
   id≤fwd⁻∘bwd-◻ (_│•_ {x = x} E F) (τ ᶜ)
      with fwd⁻ E (bwd-◻ E ([ x ] • ᵇ)) | fwd⁻ F (bwd-◻ F (• [ x ] 〈 ◻ 〉 ᶜ)) |
           id≤fwd⁻∘bwd-◻ E ([ x ] • ᵇ) | id≤fwd⁻∘bwd-◻ F (• [ x ] 〈 ◻ 〉 ᶜ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) ([ x ] • ᵇ) | inspect (fwd⁻ F ∘ᶠ bwd-◻ F) (• [ x ] 〈 ◻ 〉 ᶜ)
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ | [ [ ._ ] • ᵇ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ]
       | [ eq ] | [ eq′ ] rewrite eq | eq′ = [ τ ᶜ ]
   id≤fwd⁻∘bwd-◻ (_│ᵥ_ {x = x} E F) (τ ᶜ)
      with fwd⁻ E (bwd-◻ E ([ x ] • ᵇ)) | fwd⁻ F (bwd-◻ F ((• [ x ]) ᵇ)) |
           id≤fwd⁻∘bwd-◻ E ([ x ] • ᵇ) | id≤fwd⁻∘bwd-◻ F ((• [ x ]) ᵇ)
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ (• [ ._ ]) ᵇ ] = [ τ ᶜ ]
   id≤fwd⁻∘bwd-◻ (ν•_ {x = x} E) ((• _) ᵇ)
      with fwd⁻ E (bwd-◻ E (• suc [ x ] 〈 zero 〉 ᶜ)) | id≤fwd⁻∘bwd-◻ E (• suc [ x ] 〈 zero 〉 ᶜ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) (• suc [ x ] 〈 zero 〉 ᶜ)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ eq ] rewrite eq = top ((• x) ᵇ)
   id≤fwd⁻∘bwd-◻ {a = x • ᵇ} (νᵇ E) (_ • ᵇ)
      with fwd⁻ E (bwd-◻ E ([ (push *) x ] • ᵇ)) | id≤fwd⁻∘bwd-◻ E ([ (push *) x ] • ᵇ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) ([ (push *) x ] • ᵇ)
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ eq ] rewrite eq = top (x • ᵇ)
   id≤fwd⁻∘bwd-◻ {a = (• x) ᵇ} (νᵇ E) ((• _) ᵇ)
      with fwd⁻ E (bwd-◻ E ((• [ (push *) x ]) ᵇ)) | id≤fwd⁻∘bwd-◻ E ((• [ (push *) x ]) ᵇ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) ((• [ (push *) x ]) ᵇ)
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] | [ eq ] rewrite eq = top ((• x) ᵇ)
   id≤fwd⁻∘bwd-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• _ 〈 _ 〉 ᶜ)
      with fwd⁻ E (bwd-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ)) | id≤fwd⁻∘bwd-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ eq ] rewrite eq = top (• x 〈 y 〉 ᶜ)
   id≤fwd⁻∘bwd-◻ {a = τ ᶜ} (νᶜ E) (τ ᶜ)
      with fwd⁻ E (bwd-◻ E (τ ᶜ)) | id≤fwd⁻∘bwd-◻ E (τ ᶜ) | inspect (fwd⁻ E ∘ᶠ bwd-◻ E) (τ ᶜ)
   ... | [ τ ᶜ ] , _ | [ _ ] | [ eq ] rewrite eq = [ τ ᶜ ]
   id≤fwd⁻∘bwd-◻ (! E) a with bwd-◻ E a | id≤fwd⁻∘bwd-◻ E a
   ... | R │ ◻ | a′ = ≤-trans a′ (π₁ (fwd⁻ᴹ E (ᴹ R │ ◻)))
   ... | R │ [ ! R′ ] | a′ = ≤-trans a′ (π₁ (fwd⁻ᴹ E (R ⊔ʳ R′ │ [ ! (R ⊔ˡ R′) ])))

   id≤fwd⁻∘bwd⁻ (_ •∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (_ •∙ _) [ x • ᵇ ] R = [ ᴹ x • ᵇ ] , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (• _ 〈 _ 〉∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (• _ 〈 _ 〉∙ ._) [ • x 〈 y 〉 ᶜ ] R = ᴹ [ • x 〈 y 〉 ᶜ ] , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (E ➕₁ Q) a R = id≤fwd⁻∘bwd⁻ E a R
   id≤fwd⁻∘bwd⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) =
      let a′ , P′ = id≤fwd∘bwd E (a , R); ρ , Q′ = (ᴿ.push †) Q S in
      a′ , [ P′ │ ≤-trans (id≤ren∘unren push Q S) ((ᴿ̃.top push *ᴹ) (ᴹ Q′)) ]
   id≤fwd⁻∘bwd⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) =
      let a′ , P′ = id≤fwd∘bwd E (a , R) in a′ , [ P′ │ ᴹ S ]
   id≤fwd⁻∘bwd⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) =
      let a′ , Q′ = id≤fwd∘bwd E (a , S); ρ , P′ = (push †) P R in
      a′ , [ ≤-trans (id≤ren∘unren push P R) ((ᴿ̃.top push *ᴹ) (ᴹ P′)) │ Q′ ]
   id≤fwd⁻∘bwd⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) =
      let a′ , Q′ = id≤fwd∘bwd E (a , S) in a′ , [ ᴹ R │ Q′ ]
   id≤fwd⁻∘bwd⁻ (_│•_ {R = P′} {x = x} {y} E F) a (R │ S)
      with (pop y †) P′ R | id≤ren∘unren (pop y) P′ R
   ... | pop-y , R′ | R″
      with fwd E (bwd E ([ [ x ] • ᵇ ] , R′)) | fwd F (bwd F ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)) |
           id≤fwd∘bwd E ([ [ x ] • ᵇ ] , R′) | id≤fwd∘bwd F ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S) |
           inspect (fwd E ∘ᶠ bwd E) ([ [ x ] • ᵇ ] , R′) | inspect (fwd F ∘ᶠ bwd F) ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)
   ... | [ [ .x ] • ᵇ ] , _ | [ • [ .x ] 〈 y′ 〉 ᶜ ] , _ | [ [ .x ] • ᵇ ] , P | [ • [ .x ] 〈 v′ 〉 ᶜ ] , Q
       | [ eq ] | [ eq′ ] rewrite eq | eq′
      with ≤-trans R″ ((≤-trans pop-top (ᴿ̃.popᴹ v′) *ᴹ) (≤-trans (ᴹ R′) P))
   ... | P″ = top (τ ᶜ) , [ P″ │ Q ]
   id≤fwd⁻∘bwd⁻ (_│ᵥ_ {x = x} E F) a (ν ◻)
      with fwd⁻ E (bwd-◻ E ([ x ] • ᵇ)) | fwd⁻ F (bwd-◻ F ((• [ x ]) ᵇ)) |
           id≤fwd⁻∘bwd-◻ E ([ x ] • ᵇ) | id≤fwd⁻∘bwd-◻ F ((• [ x ]) ᵇ)
   ... | [ [ .x ] • ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ (• [ .x ]) ᵇ ] = top (τ ᶜ) , [ ν ◻ ]
   id≤fwd⁻∘bwd⁻ (_│ᵥ_ {x = x} E F) a (ν [ R │ S ])
      with fwd E (bwd E ([ [ x ] • ᵇ ] , R)) | fwd F (bwd F ([ (• [ x ]) ᵇ ] , S)) |
           id≤fwd∘bwd E ([ [ x ] • ᵇ ] , R) | id≤fwd∘bwd F ([ (• [ x ]) ᵇ ] , S) |
           inspect (fwd E ∘ᶠ bwd E) ([ [ x ] • ᵇ ] , R) | inspect (fwd F ∘ᶠ bwd F) ([ (• [ x ]) ᵇ ] , S)
   ... | [ [ .x ] • ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P | [ (• [ ._ ]) ᵇ ] , Q
       | [ eq ] | [ eq′ ] rewrite eq | eq′ = top (τ ᶜ) , [ ν [ P │ Q ] ]
   id≤fwd⁻∘bwd⁻ (ν•_ {x = x} E) a R
      with fwd⁻ E (bwd⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ] R) | id≤fwd⁻∘bwd⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ] R |
           inspect (fwd⁻ E ∘ᶠ bwd⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ]) R
   ... | [ • [ ._ ] 〈 ._ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P | [ eq ] rewrite eq = top ((• x) ᵇ) , P
   id≤fwd⁻∘bwd⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R)
      with ((swap †) P′ R) | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with fwd E (bwd E ([ [ (push *) x ] • ᵇ ] , R′)) | id≤fwd∘bwd E ([ [ (push *) x ] • ᵇ ] , R′) |
           inspect (fwd E ∘ᶠ bwd E) ([ [ (push *) x ] • ᵇ ] , R′)
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P | [ eq ] rewrite eq = top _ , [ ν ≤-trans R″ ((ᴿ̃.top swap *ᴹ) P) ]
   id≤fwd⁻∘bwd⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R)
      with ((swap †) P′ R) | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with fwd E (bwd E ([ (• [ (push *) x ]) ᵇ ] , R′)) | id≤fwd∘bwd E ([ (• [ (push *) x ]) ᵇ ] , R′) |
           inspect (fwd E ∘ᶠ bwd E) ([ (• [ (push *) x ]) ᵇ ] , R′)
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , P | [ eq ] rewrite eq = top ((• x) ᵇ) , [ ν ≤-trans R″ ((ᴿ̃.top swap *ᴹ) P) ]
   id≤fwd⁻∘bwd⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R)
      with fwd E (bwd E ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R)) |
           id≤fwd∘bwd E ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R) |
           inspect (fwd E ∘ᶠ bwd E) ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P | [ eq ] rewrite eq = top (• x 〈 y 〉 ᶜ) , [ ν P ]
   id≤fwd⁻∘bwd⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R)
      with fwd E (bwd E ([ τ ᶜ ] , R)) | id≤fwd∘bwd E ([ τ ᶜ ] , R) | inspect (fwd E ∘ᶠ bwd E) ([ τ ᶜ ] , R)
   ... | [ τ ᶜ ] , _ | [ _ ] , P | [ eq ] rewrite eq = top (τ ᶜ) , [ ν P ]
   id≤fwd⁻∘bwd⁻ (! E) a R with bwd⁻ E a R | id≤fwd⁻∘bwd⁻ E a R
   ... | R′ │ ◻ | a′ , P = ≤-trans (a′ , P) (fwdᴹ E [ ᴹ R′ │ ◻ ])
   ... | R′ │ [ ! R″ ] | a′ , P = ≤-trans (a′ , P) (fwdᴹ E [ R′ ⊔ʳ R″ │ [ ! (R′ ⊔ˡ R″) ] ])

   bwd∘fwd≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓ P) → (bwd E ∘ᶠ fwd E) P′ ≤ P′
   bwd∘fwd⁻≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓⁻ P) → (bwd E ∘ᶠ fwd⁻ E) P′ ≤ [ P′ ]

   bwd∘fwd≤id E [ P ] = bwd∘fwd⁻≤id E P
   bwd∘fwd≤id {a = _ ᵇ} _ ◻ = ◻
   bwd∘fwd≤id {a = _ ᶜ} _ ◻ = ◻

   bwd∘fwd⁻≤id (_ •∙ _) (x •∙ ◻) = [ ᴹ x •∙ ◻ ]
   bwd∘fwd⁻≤id (_ •∙ _) (x •∙ [ R ]) = [ ᴹ x •∙ ᴹ [ R ] ]
   bwd∘fwd⁻≤id (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ ◻) = [ • ᴹ x 〈 ᴹ y 〉∙ ◻ ]
   bwd∘fwd⁻≤id (• _ 〈 _ 〉∙ ._) (• x 〈 y 〉∙ [ R ]) = [ • ᴹ x 〈 ᴹ y 〉∙ ᴹ [ R ] ]
   bwd∘fwd⁻≤id (E ➕₁ _) (R ➕ _) with fwd E R | bwd∘fwd≤id E R
   ... | _ , [ _ ] | P = [ P ➕ ◻ ]
   ... | [ _ ] , ◻ | P = [ P ➕ ◻ ]
   ... | ◻ , ◻ | _ = ◻
   bwd∘fwd⁻≤id {a = _ ᵇ} (E ᵇ│ Q) (R │ S) with fwd E R | bwd∘fwd≤id E R | π₂ (unren∘ren≤id ᴿ̃.push S)
   ... | _ , [ _ ] | P | Q′ = [ P │ Q′ ]
   ... | [ _ ] , _ | P | Q′ = [ P │ Q′ ]
   ... | ◻ , ◻ | _ | Q′ = [ ◻ │ Q′ ]
   bwd∘fwd⁻≤id {a = _ ᶜ} (E ᶜ│ Q) (R │ S) with fwd E R | bwd∘fwd≤id E R
   ... | _ , [ _ ] | P = [ P │ ᴹ S ]
   ... | [ _ ] , _ | P = [ P │ ᴹ S ]
   ... | ◻ , ◻ | _ = [ ◻ │ ᴹ S ]
   bwd∘fwd⁻≤id {a = _ ᵇ} (P │ᵇ E) (R │ S) with π₂ (unren∘ren≤id ᴿ̃.push R) | fwd E S | bwd∘fwd≤id E S
   ... | P′ | _ , [ _ ] | Q = [ P′ │ Q ]
   ... | P′ |  [ _ ] , _ | Q = [ P′ │ Q ]
   ... | P′ | ◻ , ◻ | _ = [ P′ │ ◻ ]
   bwd∘fwd⁻≤id {a = _ ᶜ} (P │ᶜ E) (R │ S) with fwd E S | bwd∘fwd≤id E S
   ... | _ , [ _ ] | Q = [ ᴹ R │ Q ]
   ... | [ _ ] , _ | Q = [ ᴹ R │ Q ]
   ... | ◻ , ◻ | _ = [ ᴹ R │ ◻ ]
   bwd∘fwd⁻≤id (_│•_ {R = P′} {y = y} E F) (R │ S)
      with fwd E R | fwd F S | bwd∘fwd≤id E R | bwd∘fwd≤id F S | inspect (fwd E) R | inspect (fwd F) S
   ... | ◻ , _ | _ , _ | _ | _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | ◻ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , R′ | [ • [ ._ ] 〈 v 〉 ᶜ ] , S′ | P | Q | [ eq ] | [ eq′ ] rewrite eq | eq′
      with unren∘ren≤id (ᴿ̃.pop v) R′
   ... | pop-v , P″ =
      [ (≤-trans (bwdᴹ E ([ [ _ ] • ᵇ ] , P″)) P) │ ≤-trans (bwdᴹ F ([ • [ _ ] 〈 pop-v ᴺ.zero 〉 ᶜ ] , ᴹ S′)) Q ]
   bwd∘fwd⁻≤id (E │ᵥ F) (R │ S)
      with fwd E R | fwd F S | bwd∘fwd≤id E R | bwd∘fwd≤id F S | inspect (fwd E) R | inspect (fwd F) S
   ... | ◻ , _ | _ | _ | _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | ◻ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | P | Q | [ eq ] | [ eq′ ] rewrite eq | eq′ = [ P │ Q ]
   bwd∘fwd⁻≤id (ν• E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , ◻ | P | [ eq ] rewrite eq = [ ν P ]
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , [ _ ] | P | [ eq ] rewrite eq = [ ν P ]
   bwd∘fwd⁻≤id {a = x • ᵇ} (νᵇ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , R′ | P | [ eq ] rewrite eq =
      [ ν ≤-trans (bwdᴹ E ([ [ (push *) x ] • ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   bwd∘fwd⁻≤id {a = (• x) ᵇ} (νᵇ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] , _ | _ | _ = ◻
   ... | [ (• [ ._ ]) ᵇ ] , R′ | P | [ eq ] rewrite eq =
      [ ν ≤-trans (bwdᴹ E ([ (• [ (push *) x ]) ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   bwd∘fwd⁻≤id {a = • _ 〈 _ 〉 ᶜ} (νᶜ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | P | [ eq ] rewrite eq = [ ν P ]
   bwd∘fwd⁻≤id {a = τ ᶜ} (νᶜ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ τ ᶜ ] , R′ | P | [ eq ] rewrite eq = [ ν P ]
   bwd∘fwd⁻≤id (! E) (! R) with fwd E [ R │ [ ! R ] ] | bwd∘fwd≤id E [ R │ [ ! R ] ]
   ... | ◻ , ◻ | _ = ◻
   ... | [ a ] , ◻ | _ with bwd-◻ E a
   bwd∘fwd⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ _ ] | _ │ ◻ = [ ! R ]
   bwd∘fwd⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]
   bwd∘fwd⁻≤id (! E) (! _) | a , [ R ] | _ with bwd⁻ E a R
   bwd∘fwd⁻≤id (! _) (! _) | a , [ _ ] | [ R │ _ ] | _ │ ◻ = [ ! R ]
   bwd∘fwd⁻≤id (! _) (! _) | a , [ _ ] | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]

   gc : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) →
        IsGaloisConnection (poset {a = P}) (poset {a = a , R}) (fwd E) (bwd E)
   gc E = record {
         f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ fwdᴹ E ∘ᶠ ≤ᴸ⇒≤;
         g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ bwdᴹ E ∘ᶠ ≤ᴸ⇒≤;
         id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤fwd∘bwd E;
         g∘f≤id = ≤⇒≤ᴸ ∘ᶠ bwd∘fwd≤id E
      }
