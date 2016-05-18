module Proc.Ren.Lattice where

   open import ConcurrentSlicingCommon

   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤⁻_; open ᴾ̃._≤_
   open import Ren as ᴿ using (Ren);
     open ᴿ.Renameable ⦃...⦄
       renaming (_* to _*′; *-preserves-≃ₑ to *′-preserves-≃ₑ; *-preserves-∘ to *′-preserves-∘; *-preserves-id to *′-preserves-id)
   open import Ren.Lattice as ᴿ̃ using (suc; suc-preserves-≃ₑ; sucᴹ; pre; preᴹ; _↦_; _↦ᴹ_; _⁻¹[_]_; _⁻¹ᴹ[_]_)

   -- Functor-like, but not quite sure how to treat this as a functor in the usual sense.
   infixr 8 _*⁻ _*
   _*⁻ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} → ↓ ρ → ↓⁻ P → ↓⁻ (ρ *′) P
   _* : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P : Proc Γ} → ↓ ρ → ↓ P → ↓ (ρ *′) P

   (ρ *⁻) Ο = Ο
   (ρ *⁻) (x •∙ P) = (ρ ᴿ̃.*) x •∙ (suc ρ *) P
   (ρ *⁻) (• x 〈 y 〉∙ P) = • (ρ ᴿ̃.*) x 〈 (ρ ᴿ̃.*) y 〉∙ (ρ *) P
   (ρ *⁻) (P ➕ Q) = (ρ *) P ➕ (ρ *) Q
   (ρ *⁻) (P │ Q) = (ρ *) P │ (ρ *) Q
   (ρ *⁻) (ν P) = ν (suc ρ *) P
   (ρ *⁻) (! P) = ! (ρ *) P

   (ρ *) ◻ = ◻
   (ρ *) [ P ] = [ (ρ *⁻) P ]

   postulate
      *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ₀ σ₀ : Ren Γ Γ′} {P : Proc Γ} {ρ : ↓ ρ₀} {σ : ↓ σ₀} →
                       (∀ x → ρ x ≅ σ x) → (P′ : ↓ P) → (ρ *) P′ ≅ (σ *) P′
{-
   *-preserves-≃ₑ ρ ◻ = {!!}
   *-preserves-≃ₑ {P = Ο} _ [ Ο ] = ≅-refl
   *-preserves-≃ₑ {P = _ •∙ _} ρ [ x •∙ P ] = {!!}
   *-preserves-≃ₑ {P = • _ 〈 _ 〉∙ _} ρ [ • x 〈 y 〉∙ P ] = {!!}
   *-preserves-≃ₑ {P = _ ➕ _} ρ [ P ➕ Q ] = {!!}
   *-preserves-≃ₑ {P = _ │ _} ρ [ P │ Q ] = {!!}
   *-preserves-≃ₑ {P = ν _} ρ [ ν P ] = {!!}
   *-preserves-≃ₑ {P = ! _} ρ [ ! P ] = {!!}
-}
   postulate
      *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ₀ : Ren Δ Γ′} {σ₀ : Ren Γ Δ} {P : Proc Γ} {ρ : ↓ ρ₀} {σ : ↓ σ₀}
                      (P′ : ↓ P) → (ρ *) ((σ *) P′) ≅ (((ρ ᴿ̃.*) ∘ᶠ σ) *) P′

   wibble : ∀ {Γ} {P₀ P₀′ : Proc Γ} → P₀ ≡ P₀′ → _≅_ {A = ↓ P₀} (◻ {P = P₀}) {↓ P₀′} (◻ {P = P₀′})
   wibble {P₀ = P₀} {.P₀} refl = ≅-refl

   jibble : ∀ {Γ} {P₀ P₀′ : Proc Γ} → P₀ ≡ P₀′ → {P : ↓ P₀} {P′ : ↓ P₀′} →
            P ≅ P′ → _≅_ {A = ↓⁻_ {A = Proc Γ} (! P₀)} (! P) {↓⁻_ {A = Proc Γ} (! P₀′)} (! P′)
   jibble refl ≅-refl = ≅-refl

   *-preserves-id : ∀ {Γ} {P : Proc Γ} (P′ : ↓ P) → (ᴿ̃.id *) P′ ≅ P′
   *-preserves-id {P = P₀} ◻ = wibble (*′-preserves-id P₀)
   *-preserves-id [ Ο ] = ≅-refl
   *-preserves-id [ x •∙ P ] = {!!}
   *-preserves-id [ • x 〈 y 〉∙ P ] = {!!}
   *-preserves-id [ P ➕ Q ] = {!!}
   *-preserves-id [ P │ Q ] = {!!}
   *-preserves-id [ ν P ] = {!!}
   *-preserves-id {Γ} {P = ! P₀} [ ! P ] =
      let q = (ᴿ̃.id *) P ≅ P
          q = *-preserves-id P
          r : _≅_ {A = ↓⁻_ {A = Proc Γ} (! (idᶠ *′) P₀)} (! (ᴿ̃.id *) P) {↓⁻_ {A = Proc Γ} (! P₀)} (! P)
          r = jibble (*′-preserves-id P₀) q
          s : _≅_ {A = ↓_ {A = Proc Γ} (! (idᶠ *′) P₀)} [ ! (ᴿ̃.id *) P ] {↓_ {A = Proc Γ} (! P₀)} [ ! P ]
          s = {!!}
      in s

   infixr 8 _*⁻ᴹ _*ᴹ
   _*ᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {P₀ : Proc Γ} {ρ ρ′ : ↓ ρ₀} {P P′ : ↓ P₀} → ρ ≤ ρ′ → P ≤ P′ → (ρ *) P ≤ (ρ′ *) P′
   _*⁻ᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {P₀ : Proc Γ} {ρ ρ′ : ↓ ρ₀} {P P′ : ↓⁻ P₀} → ρ ≤ ρ′ → P ≤⁻ P′ → (ρ *⁻) P ≤⁻ (ρ′ *⁻) P′

   (ρ *⁻ᴹ) Ο = Ο
   (ρ *⁻ᴹ) (x •∙ P) =  (ρ ᴿ̃.*ᴹ) x •∙ (sucᴹ ρ *ᴹ) P
   (ρ *⁻ᴹ) (• x 〈 y 〉∙ P) = • (ρ ᴿ̃.*ᴹ) x 〈 (ρ ᴿ̃.*ᴹ) y 〉∙ (ρ *ᴹ) P
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
   (ρ †⁻) (x •∙ P) (u •∙ P′) =
      let ρ′ , P″ = (ᴿ.suc ρ †) P P′ in pre ρ′ ⊔ (x ↦ u) , ρ ⁻¹[ x ] u •∙ P″
   (ρ †⁻) (• x 〈 y 〉∙ P) (• u 〈 v 〉∙ P′) =
      let ρ′ , P″ = (ρ †) P P′ in ρ′ ⊔ x ↦ u ⊔ y ↦ v , • ρ ⁻¹[ x ] u 〈 ρ ⁻¹[ y ] v 〉∙ P″
   (ρ †⁻) (P ➕ Q) (P′ ➕ Q′) = let ρ₁ , P″ = (ρ †) P P′; ρ₂ , Q″ = (ρ †) Q Q′ in ρ₁ ⊔ ρ₂ , P″ ➕ Q″
   (ρ †⁻) (P │ Q) (P′ │ Q′) = let ρ₁ , P″ = (ρ †) P P′; ρ₂ , Q″ = (ρ †) Q Q′ in ρ₁ ⊔ ρ₂ , P″ │ Q″
   (ρ †⁻) (ν P) (ν P′) = let ρ′ , P″ = (ᴿ.suc ρ †) P P′ in pre ρ′ , ν P″
   (ρ †⁻) (! P) (! P′) = let ρ′ , P″ = (ρ †) P P′ in ρ′ , ! P″

   (_ †) _ ◻ = ᴿ̃.◻ , ◻
   (ρ †) P [ P′ ] = map idᶠ [_] ((ρ †⁻) P P′)

   _†⁻ᴹ : ∀ {Γ Γ′} (ρ₀ : Ren Γ Γ′) (P₀ : Proc Γ) {P P′ : ↓⁻ (ρ₀ *′) P₀} → P ≤⁻ P′ → (ρ₀ †⁻) P₀ P ≤⁻ (ρ₀ †⁻) P₀ P′
   _†ᴹ : ∀ {Γ Γ′} (ρ₀ : Ren Γ Γ′) (P₀ : Proc Γ) {P P′ : ↓ (ρ₀ *′) P₀} → P ≤ P′ → (ρ₀ †) P₀ P ≤ (ρ₀ †) P₀ P′
   (ρ †⁻ᴹ) Ο Ο = ᴿ̃.◻≤ , Ο
   (ρ †⁻ᴹ) (x •∙ P) (u •∙ P′) =
      let ρ′ , P″ = (ᴿ.suc ρ †ᴹ) P P′ in preᴹ ρ′ ⊔ᴹ x ↦ᴹ u , ρ ⁻¹ᴹ[ x ] u •∙ P″
   (ρ †⁻ᴹ) (• x 〈 y 〉∙ P) (• u 〈 v 〉∙ P′) =
      let ρ′ , P″ = (ρ †ᴹ) P P′ in ρ′ ⊔ᴹ x ↦ᴹ u ⊔ᴹ y ↦ᴹ v , • ρ ⁻¹ᴹ[ x ] u 〈 ρ ⁻¹ᴹ[ y ] v 〉∙ P″
   (ρ †⁻ᴹ) (P ➕ Q) (P′ ➕ Q′) = let ρ₁ , P″ = (ρ †ᴹ) P P′; ρ₂ , Q″ = (ρ †ᴹ) Q Q′ in ρ₁ ⊔ᴹ ρ₂ , P″ ➕ Q″
   (ρ †⁻ᴹ) (P │ Q) (P′ │ Q′) = let ρ₁ , P″ = (ρ †ᴹ) P P′; ρ₂ , Q″ = (ρ †ᴹ) Q Q′ in ρ₁ ⊔ᴹ ρ₂ , P″ │ Q″
   (ρ †⁻ᴹ) (ν P) (ν P′) = let ρ′ , P″ = (ᴿ.suc ρ †ᴹ) P P′ in preᴹ ρ′ , ν P″
   (ρ †⁻ᴹ) (! P) (! P′) = let ρ′ , P″ = (ρ †ᴹ) P P′ in ρ′ , ! P″

   (_ †ᴹ) _ ◻ = ᴿ̃.◻≤ , ◻
   (ρ †ᴹ) P [ P′ ] = map idᶠ [_] ((ρ †⁻ᴹ) P P′)
