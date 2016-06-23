module Transition.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra
   open import Ext.Algebra.Structures

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Lattice as ᴬ̃ using (top; ↓ᵇ_; ↓ᶜ_);
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ_; open ᴬ̃._≤ᶜ_
   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Proc using (Proc)
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (unren; unrenᴹ; _*ᴹ) renaming (_* to _*̃)
   open import Proc.Ren.Lattice.GaloisConnection using (id≤ren∘unren; unren∘ren≤id)
   import Name as ᴺ
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Ren as ᴿ using (push; pop; swap; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (pop-top)
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Lattice as ᵀ̃ using (step; stepᴹ; step⁻; step⁻ᴹ; unstep; unstepᴹ; unstep-◻; unstep⁻)

   id≤step∘unstep : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (aR : ↓ (a , R)) → aR ≤ (step E ∘ᶠ unstep E) aR
   id≤step⁻∘unstep-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓⁻ a) → [ a′ ] ≤ π₁ (step⁻ E (unstep-◻ E a′))
   id≤step⁻∘unstep⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓ a) (R′ : ↓⁻ R) → (a′ , [ R′ ]) ≤ step⁻ E (unstep⁻ E a′ R′)

   id≤step∘unstep E (a , [ R ]) = id≤step⁻∘unstep⁻ E a R
   id≤step∘unstep E ([ a ] , ◻) = id≤step⁻∘unstep-◻ E a , ◻
   id≤step∘unstep _ (◻ , ◻) = ◻ , ◻

   id≤step⁻∘unstep-◻ (_ •∙ _) (x • ᵇ) = [ ᴹ x • ᵇ ]
   id≤step⁻∘unstep-◻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = [ • ᴹ x 〈 ᴹ y 〉 ᶜ ]
   id≤step⁻∘unstep-◻ (E ➕₁ Q) a = id≤step⁻∘unstep-◻ E a
   id≤step⁻∘unstep-◻ (E ᵇ│ Q) (a ᵇ) = id≤step⁻∘unstep-◻ E (a ᵇ)
   id≤step⁻∘unstep-◻ (E ᶜ│ Q) (a ᶜ) = id≤step⁻∘unstep-◻ E (a ᶜ)
   id≤step⁻∘unstep-◻ (P │ᵇ E) (a ᵇ) = id≤step⁻∘unstep-◻ E (a ᵇ)
   id≤step⁻∘unstep-◻ (P │ᶜ E) (a ᶜ) = id≤step⁻∘unstep-◻ E (a ᶜ)
   id≤step⁻∘unstep-◻ (_│•_ {x = x} E F) (τ ᶜ)
      with step⁻ E (unstep-◻ E ([ x ] • ᵇ)) | step⁻ F (unstep-◻ F (• [ x ] 〈 ◻ 〉 ᶜ)) |
           id≤step⁻∘unstep-◻ E ([ x ] • ᵇ) | id≤step⁻∘unstep-◻ F (• [ x ] 〈 ◻ 〉 ᶜ) |
           inspect (step⁻ E ∘ᶠ unstep-◻ E) ([ x ] • ᵇ) | inspect (step⁻ F ∘ᶠ unstep-◻ F) (• [ x ] 〈 ◻ 〉 ᶜ)
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ | [ [ ._ ] • ᵇ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ]
       | [ eq ] | [ eq′ ] rewrite eq | eq′ = [ τ ᶜ ]
   id≤step⁻∘unstep-◻ (_│ᵥ_ {x = x} E F) (τ ᶜ)
      with step⁻ E (unstep-◻ E ([ x ] • ᵇ)) | step⁻ F (unstep-◻ F ((• [ x ]) ᵇ)) |
           id≤step⁻∘unstep-◻ E ([ x ] • ᵇ) | id≤step⁻∘unstep-◻ F ((• [ x ]) ᵇ)
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ (• [ ._ ]) ᵇ ] = [ τ ᶜ ]
   id≤step⁻∘unstep-◻ (ν•_ {x = x} E) ((• _) ᵇ)
      with step⁻ E (unstep-◻ E (• suc [ x ] 〈 zero 〉 ᶜ)) | id≤step⁻∘unstep-◻ E (• suc [ x ] 〈 zero 〉 ᶜ) |
           inspect (step⁻ E ∘ᶠ unstep-◻ E) (• suc [ x ] 〈 zero 〉 ᶜ)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ eq ] rewrite eq = top ((• x) ᵇ)
   id≤step⁻∘unstep-◻ {a = x • ᵇ} (νᵇ E) (_ • ᵇ)
      with step⁻ E (unstep-◻ E ([ (push *) x ] • ᵇ)) | id≤step⁻∘unstep-◻ E ([ (push *) x ] • ᵇ) |
           inspect (step⁻ E ∘ᶠ unstep-◻ E) ([ (push *) x ] • ᵇ)
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ eq ] rewrite eq = top (x • ᵇ)
   id≤step⁻∘unstep-◻ {a = (• x) ᵇ} (νᵇ E) ((• _) ᵇ)
      with step⁻ E (unstep-◻ E ((• [ (push *) x ]) ᵇ)) | id≤step⁻∘unstep-◻ E ((• [ (push *) x ]) ᵇ) |
           inspect (step⁻ E ∘ᶠ unstep-◻ E) ((• [ (push *) x ]) ᵇ)
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] | [ eq ] rewrite eq = top ((• x) ᵇ)
   id≤step⁻∘unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• _ 〈 _ 〉 ᶜ)
      with step⁻ E (unstep-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ)) | id≤step⁻∘unstep-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ) |
           inspect (step⁻ E ∘ᶠ unstep-◻ E) (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ eq ] rewrite eq = top (• x 〈 y 〉 ᶜ)
   id≤step⁻∘unstep-◻ {a = τ ᶜ} (νᶜ E) (τ ᶜ)
      with step⁻ E (unstep-◻ E (τ ᶜ)) | id≤step⁻∘unstep-◻ E (τ ᶜ) | inspect (step⁻ E ∘ᶠ unstep-◻ E) (τ ᶜ)
   ... | [ τ ᶜ ] , _ | [ _ ] | [ eq ] rewrite eq = [ τ ᶜ ]
   id≤step⁻∘unstep-◻ (! E) a with unstep-◻ E a | id≤step⁻∘unstep-◻ E a
   ... | R │ ◻ | a′ = ≤-trans a′ (π₁ (step⁻ᴹ E (ᴹ R │ ◻)))
   ... | R │ [ ! R′ ] | a′ = ≤-trans a′ (π₁ (step⁻ᴹ E (R ⊔ʳ R′ │ [ ! (R ⊔ˡ R′) ])))

   id≤step⁻∘unstep⁻ (_ •∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (_ •∙ _) [ x • ᵇ ] R = [ ᴹ x • ᵇ ] , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (• _ 〈 _ 〉∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (• _ 〈 _ 〉∙ ._) [ • x 〈 y 〉 ᶜ ] R = ᴹ [ • x 〈 y 〉 ᶜ ] , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (E ➕₁ Q) a R = id≤step⁻∘unstep⁻ E a R
   id≤step⁻∘unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) =
      let a′ , P′ = id≤step∘unstep E (a , R); ρ , Q′ = unren push  Q S in
      a′ , [ P′ │ ≤-trans (id≤ren∘unren push Q S) ((ᴿ̃.top push *ᴹ) (ᴹ Q′)) ]
   id≤step⁻∘unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) =
      let a′ , P′ = id≤step∘unstep E (a , R) in a′ , [ P′ │ ᴹ S ]
   id≤step⁻∘unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) =
      let a′ , Q′ = id≤step∘unstep E (a , S); ρ , P′ = unren push P R in
      a′ , [ ≤-trans (id≤ren∘unren push P R) ((ᴿ̃.top push *ᴹ) (ᴹ P′)) │ Q′ ]
   id≤step⁻∘unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) =
      let a′ , Q′ = id≤step∘unstep E (a , S) in a′ , [ ᴹ R │ Q′ ]
   id≤step⁻∘unstep⁻ (_│•_ {R = P′} {x = x} {y} E F) a (R │ S)
      with unren (pop y) P′ R | id≤ren∘unren (pop y) P′ R
   ... | pop-y , R′ | R″
      with step E (unstep E ([ [ x ] • ᵇ ] , R′)) | step F (unstep F ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)) |
           id≤step∘unstep E ([ [ x ] • ᵇ ] , R′) | id≤step∘unstep F ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S) |
           inspect (step E ∘ᶠ unstep E) ([ [ x ] • ᵇ ] , R′) | inspect (step F ∘ᶠ unstep F) ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)
   ... | [ [ .x ] • ᵇ ] , _ | [ • [ .x ] 〈 y′ 〉 ᶜ ] , _ | [ [ .x ] • ᵇ ] , P | [ • [ .x ] 〈 v′ 〉 ᶜ ] , Q
       | [ eq ] | [ eq′ ] rewrite eq | eq′
      with ≤-trans R″ ((≤-trans pop-top (ᴿ̃.popᴹ v′) *ᴹ) (≤-trans (ᴹ R′) P))
   ... | P″ = top (τ ᶜ) , [ P″ │ Q ]
   id≤step⁻∘unstep⁻ (_│ᵥ_ {x = x} E F) a (ν ◻)
      with step⁻ E (unstep-◻ E ([ x ] • ᵇ)) | step⁻ F (unstep-◻ F ((• [ x ]) ᵇ)) |
           id≤step⁻∘unstep-◻ E ([ x ] • ᵇ) | id≤step⁻∘unstep-◻ F ((• [ x ]) ᵇ)
   ... | [ [ .x ] • ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ (• [ .x ]) ᵇ ] = top (τ ᶜ) , [ ν ◻ ]
   id≤step⁻∘unstep⁻ (_│ᵥ_ {x = x} E F) a (ν [ R │ S ])
      with step E (unstep E ([ [ x ] • ᵇ ] , R)) | step F (unstep F ([ (• [ x ]) ᵇ ] , S)) |
           id≤step∘unstep E ([ [ x ] • ᵇ ] , R) | id≤step∘unstep F ([ (• [ x ]) ᵇ ] , S) |
           inspect (step E ∘ᶠ unstep E) ([ [ x ] • ᵇ ] , R) | inspect (step F ∘ᶠ unstep F) ([ (• [ x ]) ᵇ ] , S)
   ... | [ [ .x ] • ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P | [ (• [ ._ ]) ᵇ ] , Q
       | [ eq ] | [ eq′ ] rewrite eq | eq′ = top (τ ᶜ) , [ ν [ P │ Q ] ]
   id≤step⁻∘unstep⁻ (ν•_ {x = x} E) a R
      with step⁻ E (unstep⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ] R) | id≤step⁻∘unstep⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ] R |
           inspect (step⁻ E ∘ᶠ unstep⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ]) R
   ... | [ • [ ._ ] 〈 ._ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P | [ eq ] rewrite eq = top ((• x) ᵇ) , P
   id≤step⁻∘unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R)
      with unren swap P′ R | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with step E (unstep E ([ [ (push *) x ] • ᵇ ] , R′)) | id≤step∘unstep E ([ [ (push *) x ] • ᵇ ] , R′) |
           inspect (step E ∘ᶠ unstep E) ([ [ (push *) x ] • ᵇ ] , R′)
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P | [ eq ] rewrite eq = top _ , [ ν ≤-trans R″ ((ᴿ̃.top swap *ᴹ) P) ]
   id≤step⁻∘unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R)
      with unren swap P′ R | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with step E (unstep E ([ (• [ (push *) x ]) ᵇ ] , R′)) | id≤step∘unstep E ([ (• [ (push *) x ]) ᵇ ] , R′) |
           inspect (step E ∘ᶠ unstep E) ([ (• [ (push *) x ]) ᵇ ] , R′)
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , P | [ eq ] rewrite eq = top ((• x) ᵇ) , [ ν ≤-trans R″ ((ᴿ̃.top swap *ᴹ) P) ]
   id≤step⁻∘unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R)
      with step E (unstep E ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R)) |
           id≤step∘unstep E ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R) |
           inspect (step E ∘ᶠ unstep E) ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P | [ eq ] rewrite eq = top (• x 〈 y 〉 ᶜ) , [ ν P ]
   id≤step⁻∘unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R)
      with step E (unstep E ([ τ ᶜ ] , R)) | id≤step∘unstep E ([ τ ᶜ ] , R) | inspect (step E ∘ᶠ unstep E) ([ τ ᶜ ] , R)
   ... | [ τ ᶜ ] , _ | [ _ ] , P | [ eq ] rewrite eq = top (τ ᶜ) , [ ν P ]
   id≤step⁻∘unstep⁻ (! E) a R with unstep⁻ E a R | id≤step⁻∘unstep⁻ E a R
   ... | R′ │ ◻ | a′ , P = ≤-trans (a′ , P) (stepᴹ E [ ᴹ R′ │ ◻ ])
   ... | R′ │ [ ! R″ ] | a′ , P = ≤-trans (a′ , P) (stepᴹ E [ R′ ⊔ʳ R″ │ [ ! (R′ ⊔ˡ R″) ] ])

   unstep∘step≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓ P) → (unstep E ∘ᶠ step E) P′ ≤ P′
   unstep∘step⁻≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓⁻ P) → (unstep E ∘ᶠ step⁻ E) P′ ≤ [ P′ ]

   unstep∘step≤id E [ P ] = unstep∘step⁻≤id E P
   unstep∘step≤id {a = _ ᵇ} _ ◻ = ◻
   unstep∘step≤id {a = _ ᶜ} _ ◻ = ◻

   unstep∘step⁻≤id (_ •∙ _) (x •∙ ◻) = [ ᴹ x •∙ ◻ ]
   unstep∘step⁻≤id (_ •∙ _) (x •∙ [ R ]) = [ ᴹ x •∙ ᴹ [ R ] ]
   unstep∘step⁻≤id (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ ◻) = [ • ᴹ x 〈 ᴹ y 〉∙ ◻ ]
   unstep∘step⁻≤id (• _ 〈 _ 〉∙ ._) (• x 〈 y 〉∙ [ R ]) = [ • ᴹ x 〈 ᴹ y 〉∙ ᴹ [ R ] ]
   unstep∘step⁻≤id (E ➕₁ _) (R ➕ _) with step E R | unstep∘step≤id E R
   ... | _ , [ _ ] | P = [ P ➕ ◻ ]
   ... | [ _ ] , ◻ | P = [ P ➕ ◻ ]
   ... | ◻ , ◻ | _ = ◻
   unstep∘step⁻≤id {a = _ ᵇ} (E ᵇ│ Q) (R │ S) with step E R | unstep∘step≤id E R | π₂ (unren∘ren≤id ᴿ̃.push S)
   ... | _ , [ _ ] | P | Q′ = [ P │ Q′ ]
   ... | [ _ ] , _ | P | Q′ = [ P │ Q′ ]
   ... | ◻ , ◻ | _ | Q′ = [ ◻ │ Q′ ]
   unstep∘step⁻≤id {a = _ ᶜ} (E ᶜ│ Q) (R │ S) with step E R | unstep∘step≤id E R
   ... | _ , [ _ ] | P = [ P │ ᴹ S ]
   ... | [ _ ] , _ | P = [ P │ ᴹ S ]
   ... | ◻ , ◻ | _ = [ ◻ │ ᴹ S ]
   unstep∘step⁻≤id {a = _ ᵇ} (P │ᵇ E) (R │ S) with π₂ (unren∘ren≤id ᴿ̃.push R) | step E S | unstep∘step≤id E S
   ... | P′ | _ , [ _ ] | Q = [ P′ │ Q ]
   ... | P′ |  [ _ ] , _ | Q = [ P′ │ Q ]
   ... | P′ | ◻ , ◻ | _ = [ P′ │ ◻ ]
   unstep∘step⁻≤id {a = _ ᶜ} (P │ᶜ E) (R │ S) with step E S | unstep∘step≤id E S
   ... | _ , [ _ ] | Q = [ ᴹ R │ Q ]
   ... | [ _ ] , _ | Q = [ ᴹ R │ Q ]
   ... | ◻ , ◻ | _ = [ ᴹ R │ ◻ ]
   unstep∘step⁻≤id (_│•_ {R = P′} {y = y} E F) (R │ S)
      with step E R | step F S | unstep∘step≤id E R | unstep∘step≤id F S | inspect (step E) R | inspect (step F) S
   ... | ◻ , _ | _ , _ | _ | _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | ◻ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , R′ | [ • [ ._ ] 〈 v 〉 ᶜ ] , S′ | P | Q | [ eq ] | [ eq′ ] rewrite eq | eq′
      with unren∘ren≤id (ᴿ̃.pop v) R′
   ... | pop-v , P″ =
      [ (≤-trans (unstepᴹ E ([ [ _ ] • ᵇ ] , P″)) P) │ ≤-trans (unstepᴹ F ([ • [ _ ] 〈 pop-v ᴺ.zero 〉 ᶜ ] , ᴹ S′)) Q ]
   unstep∘step⁻≤id (E │ᵥ F) (R │ S)
      with step E R | step F S | unstep∘step≤id E R | unstep∘step≤id F S | inspect (step E) R | inspect (step F) S
   ... | ◻ , _ | _ | _ | _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | ◻ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | P | Q | [ eq ] | [ eq′ ] rewrite eq | eq′ = [ P │ Q ]
   unstep∘step⁻≤id (ν• E) (ν R) with step E R | unstep∘step≤id E R | inspect (step E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , ◻ | P | [ eq ] rewrite eq = [ ν P ]
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , [ _ ] | P | [ eq ] rewrite eq = [ ν P ]
   unstep∘step⁻≤id {a = x • ᵇ} (νᵇ E) (ν R) with step E R | unstep∘step≤id E R | inspect (step E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , R′ | P | [ eq ] rewrite eq =
      [ ν ≤-trans (unstepᴹ E ([ [ (push *) x ] • ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   unstep∘step⁻≤id {a = (• x) ᵇ} (νᵇ E) (ν R) with step E R | unstep∘step≤id E R | inspect (step E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] , _ | _ | _ = ◻
   ... | [ (• [ ._ ]) ᵇ ] , R′ | P | [ eq ] rewrite eq =
      [ ν ≤-trans (unstepᴹ E ([ (• [ (push *) x ]) ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   unstep∘step⁻≤id {a = • _ 〈 _ 〉 ᶜ} (νᶜ E) (ν R) with step E R | unstep∘step≤id E R | inspect (step E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | P | [ eq ] rewrite eq = [ ν P ]
   unstep∘step⁻≤id {a = τ ᶜ} (νᶜ E) (ν R) with step E R | unstep∘step≤id E R | inspect (step E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ τ ᶜ ] , R′ | P | [ eq ] rewrite eq = [ ν P ]
   unstep∘step⁻≤id (! E) (! R) with step E [ R │ [ ! R ] ] | unstep∘step≤id E [ R │ [ ! R ] ]
   ... | ◻ , ◻ | _ = ◻
   ... | [ a ] , ◻ | _ with unstep-◻ E a
   unstep∘step⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ _ ] | _ │ ◻ = [ ! R ]
   unstep∘step⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]
   unstep∘step⁻≤id (! E) (! _) | a , [ R ] | _ with unstep⁻ E a R
   unstep∘step⁻≤id (! _) (! _) | a , [ _ ] | [ R │ _ ] | _ │ ◻ = [ ! R ]
   unstep∘step⁻≤id (! _) (! _) | a , [ _ ] | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]

   gc : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) →
        IsGaloisConnection (poset {a = P}) (poset {a = a , R}) (step E) (unstep E)
   gc E = record {
         f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ stepᴹ E ∘ᶠ ≤ᴸ⇒≤;
         g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ unstepᴹ E ∘ᶠ ≤ᴸ⇒≤;
         id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤step∘unstep E;
         g∘f≤id = ≤⇒≤ᴸ ∘ᶠ unstep∘step≤id E
      }
