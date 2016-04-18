module Proc.Ren.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra

   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Name.Lattice
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren
   open import Proc.Ren.Lattice using (_*⁻; _*ᴹ; _†; _†ᴹ; _†⁻; ᴿᴾ-prefixes) renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (◻≤; _↦_; _⁻¹[_]_; suc; sucᴹ; pre; preᴹ)
   open import Ren.Lattice.GaloisConnection using (id≤get∘put; put∘get≤id; id≤suc∘pre; pre∘suc≡id)

   id≤ren∘unren : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (P : Proc Γ) (P′ : ↓ (ρ *) P) → let ρ′ , P″ = (ρ †) P P′ in P′ ≤ (ρ′ *̃) P″
   id≤⁻ren⁻∘unren⁻ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (P : Proc Γ) (P′ : ↓⁻ (ρ *) P) → let ρ′ , P″ = (ρ †⁻) P P′ in P′ ≤⁻ (ρ′ *⁻) P″

   id≤⁻ren⁻∘unren⁻ ρ Ο Ο = Ο
   id≤⁻ren⁻∘unren⁻ ρ (x •∙ P) (u •∙ P′) =
      let ρ′ , P″ = (ᴿ.suc ρ †) P P′ in (
      let open ≤-Reasoning in
      begin
         u
      ≤⟨ id≤get∘put x u ⟩
         (x ↦ u ᴿ̃.*) (ρ ⁻¹[ x ] u)
      ≤⟨ ((pre ρ′ ⊔ˡ x ↦ u) ᴿ̃.*ᴹ) (ᴹ (ρ ⁻¹[ x ] u)) ⟩ _
      ∎) •∙ (
      let open ≤-Reasoning in
      begin
         P′
      ≤⟨ id≤ren∘unren (ᴿ.suc ρ) P P′ ⟩
         (ρ′ *̃) P″
      ≤⟨ (id≤suc∘pre ρ′ *ᴹ) (ᴹ P″) ⟩ _
      ≤⟨ ((sucᴹ (pre ρ′ ⊔ʳ x ↦ u)) *ᴹ) (ᴹ P″) ⟩ _
      ∎)
   id≤⁻ren⁻∘unren⁻ ρ (• x 〈 y 〉∙ P) (• u 〈 v 〉∙ P′) =
      let ρ′ , P″ = (ρ †) P P′ in • (
      let open ≤-Reasoning in
      begin
         u
      ≤⟨ id≤get∘put x u ⟩
         (x ↦ u ᴿ̃.*) (ρ ⁻¹[ x ] u)
      ≤⟨ ((x ↦ u ⊔ʳ y ↦ v) ᴿ̃.*ᴹ) (ᴹ (ρ ⁻¹[ x ] u)) ⟩ _
      ≤⟨ ((ρ′ ⊔ˡ x ↦ u ⊔ y ↦ v) ᴿ̃.*ᴹ) (ᴹ (ρ ⁻¹[ x ] u)) ⟩ _
      ∎) 〈 (
      let open ≤-Reasoning in
      begin
         v
      ≤⟨ id≤get∘put y v ⟩
         (y ↦ v ᴿ̃.*) (ρ ⁻¹[ y ] v)
      ≤⟨ ((x ↦ u ⊔ˡ y ↦ v) ᴿ̃.*ᴹ) (ᴹ (ρ ⁻¹[ y ] v)) ⟩ _
      ≤⟨ ((ρ′ ⊔ˡ x ↦ u ⊔ y ↦ v) ᴿ̃.*ᴹ) (ᴹ (ρ ⁻¹[ y ] v)) ⟩ _
      ∎) 〉∙
      let open ≤-Reasoning in
      begin
         P′
      ≤⟨ id≤ren∘unren ρ P P′ ⟩
         (ρ′ *̃) P″
      ≤⟨ ((ρ′ ⊔ʳ x ↦ u ⊔ y ↦ v) *ᴹ) (ᴹ P″) ⟩ _
      ∎
   id≤⁻ren⁻∘unren⁻ ρ (P ➕ Q) (P′ ➕ Q′) =
      let ρ₁ , P″ = (ρ †) P P′; ρ₂ , Q″ = (ρ †) Q Q′; open ≤-Reasoning in
      (begin P′ ≤⟨ id≤ren∘unren ρ P P′ ⟩ (ρ₁ *̃) P″ ≤⟨ ((ρ₁ ⊔ʳ ρ₂) *ᴹ) (ᴹ P″) ⟩ _ ∎) ➕
      (begin Q′ ≤⟨ id≤ren∘unren ρ Q Q′ ⟩ (ρ₂ *̃) Q″ ≤⟨ ((ρ₁ ⊔ˡ ρ₂) *ᴹ) (ᴹ Q″) ⟩ _ ∎)
   id≤⁻ren⁻∘unren⁻ ρ (P │ Q) (P′ │ Q′) =
      let ρ₁ , P″ = (ρ †) P P′; ρ₂ , Q″ = (ρ †) Q Q′; open ≤-Reasoning in
      (begin P′ ≤⟨ id≤ren∘unren ρ P P′ ⟩ (ρ₁ *̃) P″ ≤⟨ ((ρ₁ ⊔ʳ ρ₂) *ᴹ) (ᴹ P″) ⟩ _ ∎) │
      (begin Q′ ≤⟨ id≤ren∘unren ρ Q Q′ ⟩ (ρ₂ *̃) Q″ ≤⟨ ((ρ₁ ⊔ˡ ρ₂) *ᴹ) (ᴹ Q″) ⟩ _ ∎)
   id≤⁻ren⁻∘unren⁻ ρ (ν P) (ν P′) =
      let ρ′ , P″ = (ᴿ.suc ρ †) P P′; open ≤-Reasoning in
      ν (begin P′ ≤⟨ id≤ren∘unren (ᴿ.suc ρ) P P′ ⟩ (ρ′ *̃) P″ ≤⟨ (id≤suc∘pre ρ′ *ᴹ) (ᴹ P″) ⟩ _ ∎)
   id≤⁻ren⁻∘unren⁻ ρ (! P) (! P′) = ! id≤ren∘unren ρ P P′

   id≤ren∘unren ρ P ◻ = ◻
   id≤ren∘unren ρ P [ P′ ] = [ id≤⁻ren⁻∘unren⁻ ρ P P′ ]

   unren⁻∘ren⁻≤⁻id : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} (ρ′ : ↓ ρ) (P′ : ↓⁻ P) → (ρ †⁻) P ((ρ′ *⁻) P′) ≤⁻ (ρ′ , P′)
   unren∘ren≤id : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} (ρ′ : ↓ ρ) (P′ : ↓ P) → (ρ †) P ((ρ′ *̃) P′) ≤ (ρ′ , P′)

   unren⁻∘ren⁻≤⁻id {P = Ο} ρ′ Ο = ◻≤ , Ο
   unren⁻∘ren⁻≤⁻id {ρ = ρ} {P = x •∙ P} ρ′ (u •∙ P′) =
      let ρ″ , P″ = unren∘ren≤id (suc ρ′) P′; ρ† , u′ = put∘get≤id u ρ′; open ≤-Reasoning in
      (begin _ ≤⟨ preᴹ ρ″ ⊔ᴹ ᴹ _ ⟩ _ ≤⟨ ≤-reflexive (pre∘suc≡id ρ′) ⊔-lub ρ† ⟩ _ ∎) , u′ •∙ P″
   unren⁻∘ren⁻≤⁻id {ρ = ρ} {• x 〈 y 〉∙ P} ρ′ (• u 〈 v 〉∙ P′) =
      let ρ″ , P″ = unren∘ren≤id ρ′ P′; ρ† , u′ = put∘get≤id u ρ′; ρ‡ , v′ = put∘get≤id v ρ′ in
      (ρ″ ⊔-lub ρ† ⊔-lub ρ‡) , • u′ 〈 v′ 〉∙ P″
   unren⁻∘ren⁻≤⁻id {P = P ➕ Q} ρ′ (P′ ➕ Q′) =
      let ρ₁ , P″ = unren∘ren≤id ρ′ P′; ρ₂ , Q″ = unren∘ren≤id ρ′ Q′ in (ρ₁ ⊔-lub ρ₂) , P″ ➕ Q″
   unren⁻∘ren⁻≤⁻id {P = P │ Q} ρ′ (P′ │ Q′) =
      let ρ₁ , P″ = unren∘ren≤id ρ′ P′; ρ₂ , Q″ = unren∘ren≤id ρ′ Q′ in (ρ₁ ⊔-lub ρ₂) , P″ │ Q″
   unren⁻∘ren⁻≤⁻id {P = ! P} ρ′ (! P′) = let ρ″ , P″ = unren∘ren≤id ρ′ P′ in ρ″ , ! P″
   unren⁻∘ren⁻≤⁻id {P = ν P} ρ′ (ν P′) =
      let ρ″ , P″ = unren∘ren≤id (suc ρ′) P′; open ≤-Reasoning in
      (begin _ ≤⟨ preᴹ ρ″ ⟩ _ ≤⟨ ≤-reflexive (pre∘suc≡id ρ′) ⟩ _ ∎) , ν P″
   unren∘ren≤id _ ◻ = ◻≤ , ◻
   unren∘ren≤id ρ [ P ] = map idᶠ [_] (unren⁻∘ren⁻≤⁻id ρ P)

   gc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (P : Proc Γ) → GaloisConnection (poset {a = ρ , P}) (poset {a = (ρ *) P})
   gc ρ P = ⟪ uncurry _*̃ , (ρ †) P ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ { _ _ (ρ , P) → ≤⇒≤ᴸ ((≤ᴸ⇒≤ ρ *ᴹ) (≤ᴸ⇒≤ P)) };
               g-mono = λ { _ _ P″ → let ρ , P′ = (ρ †ᴹ) P (≤ᴸ⇒≤ P″) in ≤⇒≤ᴸ ρ , ≤⇒≤ᴸ P′ };
               id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤ren∘unren ρ P;
               g∘f≤id = ≤⇒≤ᴸ ∘ᶠ uncurry unren∘ren≤id
            }
