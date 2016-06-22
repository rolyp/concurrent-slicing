module Proc.Ren.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra

   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Name.Lattice as ᴺ̃; open ᴺ̃.↓_
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren
   open import Proc.Ren.Lattice using (_*⁻; _*ᴹ; unren; unrenᴹ; unren⁻; ᴿᴾ-prefixes) renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (_̃; _̃ᴹ; ◻≤; _↦_; _⁻¹[_]_; suc; sucᴹ; pre; preᴹ)
   open import Ren.Lattice.GaloisConnection using (id≤get∘put; put₁∘get≤id; put∘get≤id; id≤suc∘pre; pre∘suc≡id)

   id≤ren∘unren : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (P : Proc Γ) (P′ : ↓ (ρ *) P) → let ρ′ , P″ = unren ρ P P′ in P′ ≤ (ρ′ *̃) P″
   id≤⁻ren⁻∘unren⁻ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (P : Proc Γ) (P′ : ↓⁻ (ρ *) P) → let ρ′ , P″ = unren⁻ ρ P P′ in P′ ≤⁻ (ρ′ *⁻) P″

   id≤⁻ren⁻∘unren⁻ ρ Ο Ο = Ο
   id≤⁻ren⁻∘unren⁻ ρ (x •∙ P) (._ •∙ P′) =
      let ρ′ , P″ = unren (ᴿ.suc ρ) P P′ in
      ρ x •∙ (let open ≤-Reasoning in
      begin
         P′
      ≤⟨ id≤ren∘unren (ᴿ.suc ρ) P P′ ⟩
         (ρ′ *̃) P″
      ≤⟨ (id≤suc∘pre ρ′ *ᴹ) (ᴹ P″) ⟩
         (suc (pre ρ′) *̃) P″
      ≤⟨ ((sucᴹ (pre ρ′ ⊔ʳ x ↦ [ ρ x ])) *ᴹ) (ᴹ P″) ⟩
         (suc (pre ρ′ ⊔ (x ↦ [ ρ x ])) *̃) P″
      ∎)
   id≤⁻ren⁻∘unren⁻ ρ (• x 〈 y 〉∙ P) (• ._ 〈 y′ 〉∙ P′) =
      let ρ′ , P″ = unren ρ P P′ in • ρ x 〈
      (let open ≤-Reasoning in
      begin
         y′
      ≤⟨ id≤get∘put y y′ ⟩
         (y ↦ y′ ̃) (ρ ⁻¹[ y ] y′)
      ≤⟨ ((ρ′ ⊔ˡ y ↦ y′) ̃ᴹ) (ᴹ (ρ ⁻¹[ y ] y′)) ⟩
         ((ρ′ ⊔ (y ↦ y′)) ̃) (ρ ⁻¹[ y ] y′)
      ∎) 〉∙
      let open ≤-Reasoning in
      begin
         P′
      ≤⟨ id≤ren∘unren ρ P P′ ⟩
         (ρ′ *̃) P″
      ≤⟨ ((ρ′ ⊔ʳ y ↦ y′) *ᴹ) (ᴹ P″) ⟩
         ((ρ′ ⊔ (y ↦ y′)) *̃) P″
      ∎
   id≤⁻ren⁻∘unren⁻ ρ (P ➕ Q) (P′ ➕ Q′) =
      let ρ₁ , P″ = unren ρ P P′; ρ₂ , Q″ = unren ρ Q Q′; open ≤-Reasoning in
      (begin P′ ≤⟨ id≤ren∘unren ρ P P′ ⟩ (ρ₁ *̃) P″ ≤⟨ ((ρ₁ ⊔ʳ ρ₂) *ᴹ) (ᴹ P″) ⟩ _ ∎) ➕
      (begin Q′ ≤⟨ id≤ren∘unren ρ Q Q′ ⟩ (ρ₂ *̃) Q″ ≤⟨ ((ρ₁ ⊔ˡ ρ₂) *ᴹ) (ᴹ Q″) ⟩ _ ∎)
   id≤⁻ren⁻∘unren⁻ ρ (P │ Q) (P′ │ Q′) =
      let ρ₁ , P″ = unren ρ P P′; ρ₂ , Q″ = unren ρ Q Q′; open ≤-Reasoning in
      (begin P′ ≤⟨ id≤ren∘unren ρ P P′ ⟩ (ρ₁ *̃) P″ ≤⟨ ((ρ₁ ⊔ʳ ρ₂) *ᴹ) (ᴹ P″) ⟩ _ ∎) │
      (begin Q′ ≤⟨ id≤ren∘unren ρ Q Q′ ⟩ (ρ₂ *̃) Q″ ≤⟨ ((ρ₁ ⊔ˡ ρ₂) *ᴹ) (ᴹ Q″) ⟩ _ ∎)
   id≤⁻ren⁻∘unren⁻ ρ (ν P) (ν P′) =
      let ρ′ , P″ = unren (ᴿ.suc ρ) P P′; open ≤-Reasoning in
      ν (begin P′ ≤⟨ id≤ren∘unren (ᴿ.suc ρ) P P′ ⟩ (ρ′ *̃) P″ ≤⟨ (id≤suc∘pre ρ′ *ᴹ) (ᴹ P″) ⟩ _ ∎)
   id≤⁻ren⁻∘unren⁻ ρ (! P) (! P′) = ! id≤ren∘unren ρ P P′

   id≤ren∘unren ρ P ◻ = ◻
   id≤ren∘unren ρ P [ P′ ] = [ id≤⁻ren⁻∘unren⁻ ρ P P′ ]

   unren⁻∘ren⁻≤⁻id : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} (ρ′ : ↓ ρ) (P′ : ↓⁻ P) → unren⁻ ρ P ((ρ′ *⁻) P′) ≤⁻ (ρ′ , P′)
   unren∘ren≤id : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} (ρ′ : ↓ ρ) (P′ : ↓ P) → unren ρ P ((ρ′ *̃) P′) ≤ (ρ′ , P′)
   unren⁻∘ren⁻≤⁻id {P = Ο} ρ′ Ο = ◻≤ , Ο
   unren⁻∘ren⁻≤⁻id {ρ = ρ} {P = x •∙ P} ρ′ (.x •∙ P′) =
      let ρ″ , P″ = unren∘ren≤id (suc ρ′) P′; ρ† = put₁∘get≤id [ x ] ρ′
          β : pre (suc ρ′) ≤ ρ′
          β = ≤-reflexive (pre∘suc≡id ρ′)
          α : pre (π₁ (unren (ᴿ.suc ρ) P ((suc ρ′ *̃) P′))) ⊔ (x ↦ [ ρ x ]) ≤ ρ′
          α = let open ≤-Reasoning in
            begin
               pre (π₁ (unren (ᴿ.suc ρ) P ((suc ρ′ *̃) P′))) ⊔ (x ↦ [ ρ x ])
            ≤⟨ preᴹ ρ″ ⊔ᴹ ᴹ (x ↦ [ ρ x ]) ⟩
               pre (suc ρ′) ⊔ (x ↦ [ ρ x ])
            ≤⟨ {!!} ⊔-lub ρ† {-≤-reflexive (pre∘suc≡id ρ′)-} ⟩
               ρ′
            ∎ in
      α , x •∙ P″
   unren⁻∘ren⁻≤⁻id {ρ = ρ} {• x 〈 y 〉∙ P} ρ′ (• ._ 〈 y′ 〉∙ P′) =
      let ρ″ , P″ = unren∘ren≤id ρ′ P′ ; ρ‡ , y″ = put∘get≤id y′ ρ′
      in ρ″ ⊔-lub ρ‡ , • x 〈 y″ 〉∙ P″
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
   gc ρ P = ⟪ uncurry _*̃ , unren ρ P ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ { _ _ (ρ , P) → ≤⇒≤ᴸ ((≤ᴸ⇒≤ ρ *ᴹ) (≤ᴸ⇒≤ P)) };
               g-mono = λ { _ _ P″ → let ρ , P′ = unrenᴹ ρ P (≤ᴸ⇒≤ P″) in ≤⇒≤ᴸ ρ , ≤⇒≤ᴸ P′ };
               id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤ren∘unren ρ P;
               g∘f≤id = ≤⇒≤ᴸ ∘ᶠ uncurry unren∘ren≤id
            }
