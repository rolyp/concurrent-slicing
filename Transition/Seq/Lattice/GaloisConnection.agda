module Transition.Seq.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   import Relation.Binary.EqReasoning as EqReasoning
   open import Ext.Algebra
   open import Ext.Algebra.Structures

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Lattice as ᴬ̃ using (↓ᵇ_; ↓ᶜ_); open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_; open ᴬ̃._≤_
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Name as ᴺ using (_+_; +-assoc)
   import Name.Lattice as ᴺ̃; open ᴺ̃.↓_
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Transition.Lattice as ᵀ̃ using (step; stepᴹ; unstep; tgt; tgtᴹ; src; srcᴹ)
   open import Transition.Lattice.GaloisConnection
      using (id≤step∘unstep; unstep∘step≤id)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_; action⋆); open ᵀ⋆._—[_]→⋆_
   open import Transition.Seq.Lattice as ᵀ̃⋆
      using (eq; adjust; adjust-removable; sym-adjust; sym-adjust-removable; ≤-preserves-≅; src⋆; src⋆ᴹ; tgt⋆; tgt⋆ᴹ)

   -- Can't think of a useful name for this thing.
   β : ∀ {Γ Δ} (eq : Γ ≡ Δ) {S : Proc Γ} (R′ : ↓ S) (R : ↓ (Proc↱ eq S)) (eq′ : R ≅ R′) →
       _≅_ {A = ↓ S} R′ {B = ↓ (Proc↱ eq S)} R
   β {Γ} {.Γ} refl R .R ≅-refl = ≅-refl

   id≤tgt⋆∘src⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → R′ ≤ (tgt⋆ E⋆ ∘ᶠ src⋆ E⋆) R′
   id≤tgt⋆∘src⋆ [] R = ᴹ R
   id≤tgt⋆∘src⋆ {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) R
      with src E (src⋆ E⋆ (sym-adjust 1 a⋆ R)) | π₂ (id≤step∘unstep E (◻ , src⋆ E⋆ (sym-adjust 1 a⋆ R)))
   ... | P | P′ =
      let S = ᵀ⋆.tgt⋆ E⋆ in
      ≤-preserves-≅ (eq 1 a⋆) (≅-sym (Proc↲ (eq 1 a⋆) S))
         (β (eq 1 a⋆) (sym-adjust 1 a⋆ R) R (sym-adjust-removable 1 a⋆ R))
         (adjust-removable 1 a⋆ (tgt⋆ E⋆ (tgt E P)))
         (≤-trans (id≤tgt⋆∘src⋆ E⋆ (sym-adjust 1 a⋆ R)) (tgt⋆ᴹ E⋆ P′))
   id≤tgt⋆∘src⋆ {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) R
      with src E (src⋆ E⋆ (sym-adjust 0 a⋆ R)) | π₂ (id≤step∘unstep E (◻ , src⋆ E⋆ (sym-adjust 0 a⋆ R)))
   ... | P | P′ =
      let S = ᵀ⋆.tgt⋆ E⋆ in
      ≤-preserves-≅ (eq 0 a⋆) (≅-sym (Proc↲ (eq 0 a⋆) S))
         (β (eq 0 a⋆) (sym-adjust 0 a⋆ R) R (sym-adjust-removable 0 a⋆ R))
         (adjust-removable 0 a⋆ (tgt⋆ E⋆ (tgt E P)))
         (≤-trans (id≤tgt⋆∘src⋆ E⋆ (sym-adjust 0 a⋆ R)) (tgt⋆ᴹ E⋆ P′))

   wib′ : ∀ {Δ Γ} (eq : Γ ≡ Δ) {S : Proc Γ} (R : ↓ Proc↱ eq S) (R′ : ↓ S) →
         _≅_ {A = ↓ S} R′ {B = ↓ (Proc↱ eq S)} R →
         _≅_ {A = ↓ S} R′ {B = ↓ S} (≅-subst✴ Proc ↓_ (sym eq) (Proc↲ eq S) R)
   wib′ refl R .R ≅-refl = ≅-refl

   src⋆∘tgt⋆≤id : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (P′ : ↓ P) → (src⋆ E⋆ ∘ᶠ tgt⋆ E⋆) P′ ≤ P′
   src⋆∘tgt⋆≤id [] P = ᴹ P
   src⋆∘tgt⋆≤id {a⋆ = _ ᵇ∷ a⋆} (E ᵇ∷ E⋆) P
      with tgt⋆ E⋆ (tgt E P) | adjust 1 a⋆ (tgt⋆ E⋆ (tgt E P)) |
           adjust-removable 1 a⋆ (tgt⋆ E⋆ (tgt E P)) | src⋆∘tgt⋆≤id E⋆ (tgt E P)
--   ... | _ | ◻ | _ | _ = ? -- ◻
--   ... | ◻ | [ _ ] | () | _
   ... | R′ | R | bib | blab =
      let jib : src E (src⋆ E⋆ (sym-adjust 1 a⋆ R)) ≤ src E (tgt E P)
          jib = ≤-preserves-≅ refl ≅-refl
             (≅-cong (λ R → src E (src⋆ E⋆ R)) (wib′ (eq 1 a⋆) R R′ bib))
             ≅-refl
             (srcᴹ E blab)
      in
      ≤-trans (≤-trans jib (srcᴹ E (ᴹ (tgt E P)))) {!!} -- (unstep∘step≤id E P)
   src⋆∘tgt⋆≤id {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) P
      with tgt⋆ E⋆ (tgt E P) | adjust 0 a⋆ (tgt⋆ E⋆ (tgt E P)) |
           adjust-removable 0 a⋆ (tgt⋆ E⋆ (tgt E P)) | src⋆∘tgt⋆≤id E⋆ (tgt E P)
--   ... | _ | ◻ | _ | _ = ◻
--   ... | ◻ | [ _ ] | () | _
   ... | R′ | R | bib | blab =
      let jib : src E (src⋆ E⋆ (sym-adjust 0 a⋆ R)) ≤ src E (tgt E P)
          jib = ≤-preserves-≅ refl ≅-refl
             (≅-cong (λ R → src E (src⋆ E⋆ R)) (wib′ (eq 0 a⋆) R R′ bib))
             ≅-refl
             (srcᴹ E blab)
      in
      ≤-trans (≤-trans jib (srcᴹ E (ᴹ (tgt E P)))) {!!} -- (unstep∘step≤id E P)

   gc : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) →
        IsGaloisConnection (poset {a = P}) (poset {a = R}) (tgt⋆ E⋆) (src⋆ E⋆)
   gc E⋆ = record {
         f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ tgt⋆ᴹ E⋆ ∘ᶠ ≤ᴸ⇒≤;
         g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ src⋆ᴹ E⋆ ∘ᶠ ≤ᴸ⇒≤;
         id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤tgt⋆∘src⋆ E⋆;
         g∘f≤id = ≤⇒≤ᴸ ∘ᶠ src⋆∘tgt⋆≤id E⋆
      }
