module Proc.Ren.Lattice where

   open import ConcurrentSlicingCommon

   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Name as ᴺ using (Name; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Name.Lattice as ᴺ̃ using (); open ᴺ̃.↓_; open ᴺ̃._≤_
   import Proc.Ren
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤⁻_; open ᴾ̃._≤_
   open import Ren as ᴿ using (Ren; +-preserves-id);
      open ᴿ.Renameable ⦃...⦄ renaming
         (_* to _*′; *-preserves-≃ₑ to *′-preserves-≃ₑ; *-preserves-∘ to *′-preserves-∘; *-preserves-id to *′-preserves-id)
   open import Ren.Lattice as ᴿ̃
      using (to-↓; to-↓-preserves-+; _ᴿ+_; suc; suc-preserves-≃ₑ; sucᴹ; pre; preᴹ; _↦_; _↦ᴹ_; _⁻¹[_]_; _⁻¹ᴹ[_]_)

   -- Functor-like, but not quite sure how to treat this as a functor in the usual sense.
   infixr 8 _*⁻ _*
   _*⁻ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} → ↓ ρ → ↓⁻ P → ↓⁻ (ρ *′) P
   _* : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} → ↓ ρ → ↓ P → ↓ (ρ *′) P

   (ρ *⁻) Ο = Ο
   (_*⁻ {ρ = ρ₀} ρ) (x •∙ P) = ρ₀ x •∙ (suc ρ *) P
   (_*⁻ {ρ = ρ₀} ρ) (• x 〈 y 〉∙ P) = • ρ₀ x 〈 (ρ ᴿ̃.*) y 〉∙ (ρ *) P
   (ρ *⁻) (P ➕ Q) = (ρ *) P ➕ (ρ *) Q
   (ρ *⁻) (P │ Q) = (ρ *) P │ (ρ *) Q
   (ρ *⁻) (ν P) = ν (suc ρ *) P
   (ρ *⁻) (! P) = ! (ρ *) P

   (ρ *) ◻ = ◻
   (ρ *) [ P ] = [ (ρ *⁻) P ]

   postulate
      *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ₀ σ₀ : Ren Γ Γ′} {P : Proc Γ} {ρ : ↓ ρ₀} {σ : ↓ σ₀} →
                       (∀ x → ρ x ≅ σ x) → (P′ : ↓ P) → (ρ *) P′ ≅ (σ *) P′
      *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ₀ : Ren Δ Γ′} {σ₀ : Ren Γ Δ} {P : Proc Γ} {ρ : ↓ ρ₀} {σ : ↓ σ₀}
                      (P′ : ↓ P) → (ρ *) ((σ *) P′) ≅ (((ρ ᴿ̃.*) ∘ᶠ σ) *) P′

   -- Rather tedious; wasn't able to usefully employ generic helpers.
   *-preserves-id : ∀ {Γ} {P : Proc Γ} (P′ : ↓ P) → (ᴿ̃.id *) P′ ≅ P′
   *-preserves-id {Γ} {P₀} ◻ = eq (*′-preserves-id P₀)
      where
         eq : ∀ {P₀ P₀′ : Proc Γ} → P₀ ≡ P₀′ → _≅_ {A = ↓ P₀} (◻ {P = P₀}) {↓ P₀′} (◻ {P = P₀′})
         eq {P₀ = P₀} {.P₀} refl = ≅-refl
   *-preserves-id [ Ο ] = ≅-refl
   *-preserves-id {Γ} {x •∙ P₀} [ .x •∙ P ] =
      eq x
         (trans (*′-preserves-≃ₑ (+-preserves-id 1) P₀) (*′-preserves-id P₀))
         (≅-trans (*-preserves-≃ₑ ᴿ̃.+-preserves-id P) (*-preserves-id P))
      where
         eq : ∀ {P₀ P₀′ : Proc (Γ + 1)} (x : Name Γ) {P : ↓ P₀} {P′ : ↓ P₀′} →
              P₀ ≡ P₀′ → P ≅ P′ → _≅_ {A = ↓_ _} [ x •∙ P ] {↓_ _} [ x •∙ P′ ]
         eq _ refl ≅-refl = ≅-refl
   *-preserves-id {Γ} {• x 〈 y₀ 〉∙ P₀} [ • .x 〈 y 〉∙ P ] =
      eq x (≡-to-≅ (ᴿ̃.*-preserves-id y)) (*′-preserves-id P₀) (*-preserves-id P)
      where
         eq : ∀ {P₀ P₀′ : Proc Γ} (x : Name Γ) {y₀ : Name Γ} {y y′ : ↓ y₀} {P : ↓ P₀} {P′ : ↓ P₀′} →
              y ≅ y′ → P₀ ≡ P₀′ → P ≅ P′ → _≅_ {A = ↓_ _} [ • x 〈 y 〉∙ P ] {↓_ _} [ • x 〈 y′ 〉∙ P′ ]
         eq _ ≅-refl refl ≅-refl = ≅-refl
   *-preserves-id {Γ} {P₀ ➕ Q₀} [ P ➕ Q ] =
      eq (*′-preserves-id P₀) (*′-preserves-id Q₀) (*-preserves-id P) (*-preserves-id Q)
      where
         eq : ∀ {P₀ P₀′ Q₀ Q₀′ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₀′} {Q : ↓ Q₀} {Q′ : ↓ Q₀′} →
              P₀ ≡ P₀′ → Q₀ ≡ Q₀′ → P ≅ P′ → Q ≅ Q′ → _≅_ {A = ↓_ _} [ P ➕ Q ] {↓_ _} [ P′ ➕ Q′ ]
         eq refl refl ≅-refl ≅-refl = ≅-refl
   *-preserves-id {Γ} {P₀ │ Q₀} [ P │ Q ] =
      eq (*′-preserves-id P₀) (*′-preserves-id Q₀) (*-preserves-id P) (*-preserves-id Q)
      where
         eq : ∀ {P₀ P₀′ Q₀ Q₀′ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₀′} {Q : ↓ Q₀} {Q′ : ↓ Q₀′} →
              P₀ ≡ P₀′ → Q₀ ≡ Q₀′ → P ≅ P′ → Q ≅ Q′ → _≅_ {A = ↓_ _} [ P │ Q ] {↓_ _} [ P′ │ Q′ ]
         eq refl refl ≅-refl ≅-refl = ≅-refl
   *-preserves-id {Γ} {ν P₀} [ ν P ] =
      eq (trans (*′-preserves-≃ₑ (+-preserves-id 1) P₀) (*′-preserves-id P₀))
         (≅-trans (*-preserves-≃ₑ ᴿ̃.+-preserves-id P) (*-preserves-id P))
      where
         eq : ∀ {P₀ P₀′ : Proc (Γ + 1)} {P : ↓ P₀} {P′ : ↓ P₀′} →
              P₀ ≡ P₀′ → P ≅ P′ → _≅_ {A = ↓_ _} [ ν P ] {↓_ _} [ ν P′ ]
         eq refl ≅-refl = ≅-refl
   *-preserves-id {Γ} { ! P₀} [ ! P ] = eq (*′-preserves-id P₀) (*-preserves-id P)
      where
         eq : ∀ {P₀ P₀′ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₀′} → P₀ ≡ P₀′ → P ≅ P′ → _≅_ {A = ↓_ _} [ ! P ] {↓_ _} [ ! P′ ]
         eq refl ≅-refl = ≅-refl

   infixr 8 _*⁻ᴹ _*ᴹ
   _*ᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {P₀ : Proc Γ} {ρ ρ′ : ↓ ρ₀} {P P′ : ↓ P₀} → ρ ≤ ρ′ → P ≤ P′ → (ρ *) P ≤ (ρ′ *) P′
   _*⁻ᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {P₀ : Proc Γ} {ρ ρ′ : ↓ ρ₀} {P P′ : ↓⁻ P₀} → ρ ≤ ρ′ → P ≤⁻ P′ → (ρ *⁻) P ≤⁻ (ρ′ *⁻) P′

   (ρ *⁻ᴹ) Ο = Ο
   (_*⁻ᴹ {ρ₀ = ρ₀} ρ) (x •∙ P) =  ρ₀ x •∙ (sucᴹ ρ *ᴹ) P
   (_*⁻ᴹ {ρ₀ = ρ₀} ρ) (• x 〈 y 〉∙ P) = • ρ₀ x 〈 (ρ ᴿ̃.*ᴹ) y 〉∙ (ρ *ᴹ) P
   (ρ *⁻ᴹ) (P ➕ Q) = (ρ *ᴹ) P ➕ (ρ *ᴹ) Q
   (ρ *⁻ᴹ) (P │ Q) = (ρ *ᴹ) P │ (ρ *ᴹ) Q
   (ρ *⁻ᴹ) (ν P) = ν (sucᴹ ρ *ᴹ) P
   (ρ *⁻ᴹ) (! P) = ! (ρ *ᴹ) P

   (ρ *ᴹ) ◻ = ◻
   (ρ *ᴹ) [ P ] = [ (ρ *⁻ᴹ) P ]

   open module Ren×Proc {Γ Γ′} = Lattice.Product (Ren Γ Γ′) (const (Proc Γ)) using (×-prefixes)

   -- Seem to need this to coerce the product instance to a more specific type.
   instance
      ᴿᴾ-prefixes : ∀ {Γ Γ′} → Lattice.Prefixes (Ren Γ Γ′ × Proc Γ)
      ᴿᴾ-prefixes = ×-prefixes

   _† : ∀ {Γ Γ′} (ρ₀ : Ren Γ Γ′) (P₀ : Proc Γ) → ↓ (ρ₀ *′) P₀ → ↓ (ρ₀ , P₀)
   _†⁻ : ∀ {Γ Γ′} (ρ₀ : Ren Γ Γ′) (P₀ : Proc Γ) → ↓⁻ (ρ₀ *′) P₀ → ↓⁻ (ρ₀ , P₀)

   (ρ †⁻) Ο Ο = ᴿ̃.◻ , Ο
   (ρ †⁻) (x •∙ P) (.(ρ x) •∙ P′) =
      let ρ′ , P″ = (ᴿ.suc ρ †) P P′ in pre ρ′ ⊔ (x ↦ [ ρ x ]) , x •∙ P″
   (ρ †⁻) (• x 〈 y 〉∙ P) (• .(ρ x) 〈 v 〉∙ P′) =
      let ρ′ , P″ = (ρ †) P P′ in ρ′ ⊔ x ↦ [ ρ x ] ⊔ y ↦ v , • x 〈 ρ ⁻¹[ y ] v 〉∙ P″
   (ρ †⁻) (P ➕ Q) (P′ ➕ Q′) = let ρ₁ , P″ = (ρ †) P P′; ρ₂ , Q″ = (ρ †) Q Q′ in ρ₁ ⊔ ρ₂ , P″ ➕ Q″
   (ρ †⁻) (P │ Q) (P′ │ Q′) = let ρ₁ , P″ = (ρ †) P P′; ρ₂ , Q″ = (ρ †) Q Q′ in ρ₁ ⊔ ρ₂ , P″ │ Q″
   (ρ †⁻) (ν P) (ν P′) = let ρ′ , P″ = (ᴿ.suc ρ †) P P′ in pre ρ′ , ν P″
   (ρ †⁻) (! P) (! P′) = let ρ′ , P″ = (ρ †) P P′ in ρ′ , ! P″

   (_ †) _ ◻ = ᴿ̃.◻ , ◻
   (ρ †) P [ P′ ] = map idᶠ [_] ((ρ †⁻) P P′)

   _†⁻ᴹ : ∀ {Γ Γ′} (ρ₀ : Ren Γ Γ′) (P₀ : Proc Γ) {P P′ : ↓⁻ (ρ₀ *′) P₀} → P ≤⁻ P′ → (ρ₀ †⁻) P₀ P ≤⁻ (ρ₀ †⁻) P₀ P′
   _†ᴹ : ∀ {Γ Γ′} (ρ₀ : Ren Γ Γ′) (P₀ : Proc Γ) {P P′ : ↓ (ρ₀ *′) P₀} → P ≤ P′ → (ρ₀ †) P₀ P ≤ (ρ₀ †) P₀ P′
   (ρ †⁻ᴹ) Ο Ο = ᴿ̃.◻≤ , Ο
   (ρ †⁻ᴹ) (x •∙ P) (.(ρ x) •∙ P′) =
      let ρ′ , P″ = (ᴿ.suc ρ †ᴹ) P P′ in preᴹ ρ′ ⊔ᴹ x ↦ᴹ [ ρ x ] , x •∙ P″
   (ρ †⁻ᴹ) (• x 〈 y 〉∙ P) (• .(ρ x) 〈 v 〉∙ P′) =
      let ρ′ , P″ = (ρ †ᴹ) P P′ in ρ′ ⊔ᴹ x ↦ᴹ [ ρ x ] ⊔ᴹ y ↦ᴹ v , • x 〈 ρ ⁻¹ᴹ[ y ] v 〉∙ P″
   (ρ †⁻ᴹ) (P ➕ Q) (P′ ➕ Q′) = let ρ₁ , P″ = (ρ †ᴹ) P P′; ρ₂ , Q″ = (ρ †ᴹ) Q Q′ in ρ₁ ⊔ᴹ ρ₂ , P″ ➕ Q″
   (ρ †⁻ᴹ) (P │ Q) (P′ │ Q′) = let ρ₁ , P″ = (ρ †ᴹ) P P′; ρ₂ , Q″ = (ρ †ᴹ) Q Q′ in ρ₁ ⊔ᴹ ρ₂ , P″ │ Q″
   (ρ †⁻ᴹ) (ν P) (ν P′) = let ρ′ , P″ = (ᴿ.suc ρ †ᴹ) P P′ in preᴹ ρ′ , ν P″
   (ρ †⁻ᴹ) (! P) (! P′) = let ρ′ , P″ = (ρ †ᴹ) P P′ in ρ′ , ! P″

   (_ †ᴹ) _ ◻ = ᴿ̃.◻≤ , ◻
   (ρ †ᴹ) P [ P′ ] = map idᶠ [_] ((ρ †⁻ᴹ) P P′)
