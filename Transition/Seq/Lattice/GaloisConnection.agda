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
      using (fwd⁻; fwd⁻ᴹ; bwd⁻; bwd⁻ᴹ; id≤fwd∘bwd; id≤fwd⁻∘bwd⁻; bwd∘fwd≤id)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_; action⋆); open ᵀ⋆._—[_]→⋆_
   open import Transition.Seq.Lattice as ᵀ̃⋆ using (source⋆; target⋆; target⋆ᴹ);
      open ᵀ̃⋆.↓_; open ᵀ̃⋆.↓⁻_; open ᵀ̃⋆._≤_; open ᵀ̃⋆._≤⁻_

   eq : ∀ Δ {Γ} (a⋆ : Action⋆ (Γ + Δ)) → Γ + Δ + inc⋆ a⋆ ≡ Γ + (Δ + inc⋆ a⋆)
   eq Δ {Γ} = +-assoc Γ Δ ∘ᶠ inc⋆

   -- TODO: give these some better or more local names!
   quib : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (_ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → ↓ (Proc↱ (eq Δ a⋆) R)
   quib Δ {a⋆ = a⋆} {R} _ = ≅-subst✴ Proc ↓_ (eq Δ a⋆) (≅-sym (Proc↲ (eq Δ a⋆) R))

   quib⁻ : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (_ : P —[ a⋆ ]→⋆ R) (R′ : ↓⁻ (Proc↱ (eq Δ a⋆) R)) → ᴾ̃.↓⁻ R
   quib⁻ Δ {a⋆ = a⋆} {R} _ = ≅-subst✴ Proc ↓⁻_ (sym (eq Δ a⋆)) (Proc↲ (eq Δ a⋆) R)

   quib⁻-removable : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓⁻ (Proc↱ (eq Δ a⋆) R)) → R′ ≅ quib⁻ Δ E⋆ R′
   quib⁻-removable Δ {a⋆ = a⋆} {R} _ = ≅-sym ∘ᶠ ≅-subst✴-removable Proc ↓⁻_ (sym (eq Δ a⋆)) (Proc↲ (eq Δ a⋆) R)

   quib-removable : ∀ Δ {Γ P} {a⋆ : Action⋆ (Γ + Δ)} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → R′ ≅ quib Δ E⋆ R′
   quib-removable Δ {a⋆ = a⋆} {R} _ = ≅-sym ∘ᶠ ≅-subst✴-removable Proc ↓_ (eq Δ a⋆) (≅-sym (Proc↲ (eq Δ a⋆) R))

   bibble : ∀ {Γ Γ′} {P₀ : Proc Γ} {Q₀ : Proc Γ′} {P P′ : ↓ P₀} {Q Q′ : ↓ Q₀} →
            Γ ≡ Γ′ → P₀ ≅ Q₀ → P ≅ Q → P′ ≅ Q′ → P ≤ P′ → Q ≤ Q′
   bibble refl ≅-refl ≅-refl ≅-refl = idᶠ

   bibble⁻ : ∀ {Γ Γ′} {P₀ : Proc Γ} {Q₀ : Proc Γ′} {P P′ : ↓⁻ P₀} {Q Q′ : ↓⁻ Q₀} →
            Γ ≡ Γ′ → P₀ ≅ Q₀ → P ≅ Q → P′ ≅ Q′ → P ≤⁻ P′ → Q ≤⁻ Q′
   bibble⁻ refl ≅-refl ≅-refl ≅-refl = idᶠ

   nibble : ∀ {Γ Δ} (eq : Γ ≡ Δ) (S : Proc Γ) (R′ : ↓⁻ S) (R : ↓⁻ (Proc↱ eq S)) (eq′ : R ≅ R′) →
            _≅_ {A = ↓ S} [ R′ ] {B = ↓ (Proc↱ eq S)} [ R ]
   nibble {Γ} {.Γ} refl _ R .R ≅-refl = ≅-refl

   -- bwd⋆ reflects ◻.
   bwd⋆⁻ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓⁻ R → ↓⁻ P
   bwd⋆⁻ [] R = R
   bwd⋆⁻ (E ᵇ∷ E⋆) R = bwd⁻ E ◻ (bwd⋆⁻ E⋆ (quib⁻ 1 E⋆ R))
   bwd⋆⁻ (E ᶜ∷ E⋆) R = bwd⁻ E ◻ (bwd⋆⁻ E⋆ (quib⁻ 0 E⋆ R))

   bwd⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓ R → ↓ P
   bwd⋆ _ ◻ = ◻
   bwd⋆ E⋆ [ R ] = [ bwd⋆⁻ E⋆ R ]

   id≤fwd⋆∘bwd⋆⁻ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓⁻ R) → [ R′ ] ≤ fwd⋆ E⋆ [ bwd⋆⁻ E⋆ R′ ]
   id≤fwd⋆∘bwd⋆⁻ [] R = [ ⁻ᴹ R ]
   id≤fwd⋆∘bwd⋆⁻ {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) R
      with bwd⁻ E ◻ (bwd⋆⁻ E⋆ (quib⁻ 1 E⋆ R)) | π₂ (id≤fwd⁻∘bwd⁻ E ◻ (bwd⋆⁻ E⋆ (quib⁻ 1 E⋆ R)))
   ... | P | blab =
      let S = ᵀ⋆.target⋆ E⋆ in
      bibble (eq 1 a⋆) (≅-sym (Proc↲ (eq 1 a⋆) S))
         (nibble (eq 1 a⋆) S (quib⁻ 1 E⋆ R) R (quib⁻-removable 1 E⋆ R))
         (quib-removable 1 E⋆ (fwd⋆ E⋆ (π₂ (fwd E [ P ]))))
         (≤-trans (id≤fwd⋆∘bwd⋆⁻ E⋆ (quib⁻ 1 E⋆ R)) (fwd⋆ᴹ E⋆ blab))
   id≤fwd⋆∘bwd⋆⁻ {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) R
      with bwd⁻ E ◻ (bwd⋆⁻ E⋆ (quib⁻ 0 E⋆ R)) | π₂ (id≤fwd⁻∘bwd⁻ E ◻ (bwd⋆⁻ E⋆ (quib⁻ 0 E⋆ R)))
   ... | P | blab =
      let S = ᵀ⋆.target⋆ E⋆ in
      bibble (eq 0 a⋆) (≅-sym (Proc↲ (eq 0 a⋆) S))
         (nibble (eq 0 a⋆) S (quib⁻ 0 E⋆ R) R (quib⁻-removable 0 E⋆ R))
         (quib-removable 0 E⋆ (fwd⋆ E⋆ (π₂ (fwd E [ P ]))))
         (≤-trans (id≤fwd⋆∘bwd⋆⁻ E⋆ (quib⁻ 0 E⋆ R)) (fwd⋆ᴹ E⋆ blab))

   wib′ : ∀ {Δ Γ} (eq : Γ ≡ Δ) {S : Proc Γ} (R : ↓⁻ Proc↱ eq S) (R′ : ↓⁻ S) →
         _≅_ {A = ↓ S} [ R′ ] {B = ↓ (Proc↱ eq S)} [ R ] →
         _≅_ {A = ↓⁻ S} R′ {B = ↓⁻ S} (≅-subst✴ Proc ↓⁻_ (sym eq) (Proc↲ eq S) R)
   wib′ refl R .R ≅-refl = ≅-refl

   id≤fwd⋆∘bwd⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (R′ : ↓ R) → R′ ≤ (fwd⋆ E⋆ ∘ᶠ bwd⋆ E⋆) R′
   id≤fwd⋆∘bwd⋆ _ ◻ = ◻
   id≤fwd⋆∘bwd⋆ E⋆ [ R ] = id≤fwd⋆∘bwd⋆⁻ E⋆ R

   bwd⋆∘fwd⋆≤id : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) (P′ : ↓ P) → (bwd⋆ E⋆ ∘ᶠ fwd⋆ E⋆) P′ ≤ P′
   bwd⋆∘fwd⋆≤id _ ◻ = ◻
   bwd⋆∘fwd⋆≤id [] [ P ] = [ ⁻ᴹ P ]
   bwd⋆∘fwd⋆≤id {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) [ P ]
      with fwd⋆ E⋆ (π₂ (fwd⁻ E P)) | quib 1 E⋆ (fwd⋆ E⋆ (π₂ (fwd⁻ E P))) |
           quib-removable 1 E⋆ (fwd⋆ E⋆ (π₂ (fwd⁻ E P))) | bwd⋆∘fwd⋆≤id E⋆ (π₂ (fwd⁻ E P))
   ... | _ | ◻ | _ | _ = ◻
   ... | ◻ | [ _ ] | () | _
   ... | [ R′ ] | [ R ] | bib | blab =
      let jib : bwd E (◻ , bwd⋆ E⋆ [ quib⁻ 1 E⋆ R ]) ≤ bwd E (◻ , π₂ (fwd⁻ E P))
          jib = bibble refl ≅-refl
             (≅-cong (λ R → bwd E (◻ , [ bwd⋆⁻ E⋆ R ])) (wib′ (eq 1 a⋆) R R′ bib))
             ≅-refl
             (bwdᴹ E (ᴹ ◻ , blab))
      in
      ≤-trans (≤-trans jib (bwdᴹ E ( ◻ , ᴹ (π₂ (fwd⁻ E P))))) (bwd∘fwd≤id E [ P ])
   bwd⋆∘fwd⋆≤id {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) [ P ]
      with fwd⋆ E⋆ (π₂ (fwd⁻ E P)) | quib 0 E⋆ (fwd⋆ E⋆ (π₂ (fwd⁻ E P))) |
           quib-removable 0 E⋆ (fwd⋆ E⋆ (π₂ (fwd⁻ E P))) | bwd⋆∘fwd⋆≤id E⋆ (π₂ (fwd⁻ E P))
   ... | _ | ◻ | _ | _ = ◻
   ... | ◻ | [ _ ] | () | _
   ... | [ R′ ] | [ R ] | bib | blab =
      let jib : bwd E (◻ , bwd⋆ E⋆ [ quib⁻ 0 E⋆ R ]) ≤ bwd E (◻ , π₂ (fwd⁻ E P))
          jib = bibble refl ≅-refl
             (≅-cong (λ R → bwd E (◻ , [ bwd⋆⁻ E⋆ R ])) (wib′ (eq 0 a⋆) R R′ bib))
             ≅-refl
             (bwdᴹ E (ᴹ ◻ , blab))
      in
      ≤-trans (≤-trans jib (bwdᴹ E ( ◻ , ᴹ (π₂ (fwd⁻ E P))))) (bwd∘fwd≤id E [ P ])

   gc : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) →
        IsGaloisConnection (poset {a = P}) (poset {a = R}) (fwd⋆ E⋆) (bwd⋆ E⋆)
   gc E⋆ = record {
         f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ fwd⋆ᴹ E⋆ ∘ᶠ ≤ᴸ⇒≤;
         g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ bwd⋆ᴹ E⋆ ∘ᶠ ≤ᴸ⇒≤;
         id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤fwd⋆∘bwd⋆ E⋆;
         g∘f≤id = ≤⇒≤ᴸ ∘ᶠ bwd⋆∘fwd⋆≤id E⋆
      }
