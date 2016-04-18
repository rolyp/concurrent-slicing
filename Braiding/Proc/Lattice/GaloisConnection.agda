-- A bound braid gives rise to a lattice isomorphism.
module Braiding.Proc.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset; trans)
   open import Ext.Algebra
   import Relation.Binary.EqReasoning as EqReasoning

   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (_+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (_≤⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (_*ᴹ)
      renaming (_* to _*̃; *-preserves-≃ₑ to *̃-preserves-≃ₑ; *-preserves-∘ to *̃-preserves-∘; *-preserves-id to *̃-preserves-id)
   open import Ren as ᴿ using (swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (to-↓; to-↓-preserves-≃ₑ)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Braiding.Proc using (_⋉̂_; module _⋉̂_; ⋉̂-sym; ⋉̂-sym-involutive); open _⋉̂_
   open import Braiding.Proc.Lattice using (_/̂_; /-ν)

   infixl 8 _/ᴹ_
   _/ᴹ_ : ∀ {Γ} {P₀ P₀′ : Proc Γ} {P P′ : ↓ P₀} → P ≤ P′ → (φ : P₀ ⋉̂ P₀′) → P /̂ φ ≤ P′ /̂ φ
   ◻ /ᴹ _ = ◻
   _/ᴹ_ {P = [ ν ◻ ]} {[ ν ◻ ]} [ ν ◻ ] (νν-swapₗ _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν ◻ ]} {[ ν [ ν _ ] ]} [ ν ◻ ] (νν-swapₗ _) = [ ν ◻ ]
   _/ᴹ_ {Γ} {P₀ = ν (ν .((swap *) P₀))} {P = [ ν [ ν P ] ]} {[ ν [ ν P′ ] ]} [ ν [ ν P† ] ] (νν-swapₗ P₀) =
        [ ν [ ν substᴹ ((ᴹ ᴿ̃.swap *ᴹ) P†) (swap-involutive P₀) ] ]
   _/ᴹ_ {P = [ ν [ _ ] ]} {[ ν ◻ ]} [ ν () ] (νν-swapₗ _)
   _/ᴹ_ {P = [ ν ◻ ]} {[ ν ◻ ]} [ ν ◻ ] (νν-swapᵣ _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν ◻ ]} {[ ν [ ν _ ] ]} [ ν ◻ ] (νν-swapᵣ _) = [ ν ◻ ]
   _/ᴹ_ {Γ} {P₀ = ν (ν .P₀)} {P = [ ν [ ν P ] ]} {[ ν [ ν P′ ] ]} [ ν [ ν P† ] ] (νν-swapᵣ P₀) =
        [ ν [ ν (ᴹ ᴿ̃.swap *ᴹ) P† ] ]
   _/ᴹ_ {P = [ ν [ _ ] ]} {[ ν ◻ ]} [ ν () ] (νν-swapᵣ _)
   [ P ➕ Q ] /ᴹ (φ ➕₁ refl) = [ P /ᴹ φ ➕ Q ]
   [ P ➕ Q ] /ᴹ (refl ➕₂ ψ) = [ P ➕ Q /ᴹ ψ ]
   [ P │ Q ] /ᴹ (φ │₁ refl) = [ P /ᴹ φ │ Q ]
   [ P │ Q ] /ᴹ (refl │₂ ψ) = [ P │ Q /ᴹ ψ ]
   [ ! P ] /ᴹ ! φ = [ ! (P /ᴹ φ) ]
   -- For ν, need to be explicit about sub-cases left implicit in the definition.
   _/ᴹ_ {P = [ ν ◻ ]} {[ ν ◻ ]} [ ν _ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ Ο ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ _ •∙ _ ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ • _ 〈 _ 〉∙ _ ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ _ ➕ _ ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ _ │ _ ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ ν _ ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν .◻ ]} {[ ν [ ! _ ] ]} [ ν ◻ ] (ν _) = [ ν ◻ ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ Ο ] ] (ν φ) = [ ν ([ Ο ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ x •∙ P ] ] (ν φ) = [ ν ([ x •∙ P ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ • x 〈 y 〉∙ P ] ] (ν φ) = [ ν ([ • x 〈 y 〉∙ P ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ P ➕ Q ] ] (ν φ) = [ ν ([ P ➕ Q ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ P │ Q ] ] (ν φ) = [ ν ([ P │ Q ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ ν P ] ] (ν φ) = [ ν ([ ν P ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν ._ ]} {[ ν [ ._ ] ]} [ ν [ ! P ] ] (ν φ) = [ ν ([ ! P ] /ᴹ φ) ]
   _/ᴹ_ {P = [ ν [ _ ] ]} {[ ν ◻ ]} [ ν () ] (ν φ)

   swap̃-inv₁ : ∀ {Γ} {P : Proc (Γ + 2)}
                (P′ : ↓ P) → subst ↓_ (swap-involutive P) ((ᴿ̃.swap *̃) ((ᴿ̃.swap *̃) P′)) ≡ P′
   swap̃-inv₁ {P = P} P′ = ≅-to-≡ (
      let open ≅-Reasoning in
      begin
         subst ↓_ (swap-involutive P) ((ᴿ̃.swap *̃) ((ᴿ̃.swap *̃) P′))
      ≅⟨ ≡-subst-removable ↓_ (swap-involutive P) _ ⟩
         (ᴿ̃.swap *̃) ((ᴿ̃.swap *̃) P′)
      ≅⟨ swap̃-involutive P′ ⟩
         P′
      ∎)

   swap̃-inv₂ : ∀ {Γ} {P : Proc (Γ + 2)}
                (P′ : ↓ (swap *) P) → (ᴿ̃.swap *̃) (subst ↓_ (swap-involutive P) ((ᴿ̃.swap *̃) P′)) ≡ P′
   swap̃-inv₂ {P = P} P′ = ≅-to-≡ (
      let open ≅-Reasoning in
      begin
         (ᴿ̃.swap *̃) (subst ↓_ (swap-involutive P) ((ᴿ̃.swap *̃) P′))
      ≅⟨ ≅-cong✴ ↓_ (sym (swap-involutive P)) (ᴿ̃.swap *̃) (≡-subst-removable ↓_ (swap-involutive P) _)  ⟩
         (ᴿ̃.swap *̃) ((ᴿ̃.swap *̃) P′)
      ≅⟨ swap̃-involutive P′ ⟩
         P′
      ∎
      )

   -- Exhibit one half of the isomorphism and then derive the other from involutivity of symmetry.
   {-# TERMINATING #-}
   iso» : ∀ {Γ} {P₀ P₀′ : Proc Γ} (P : ↓ P₀′) (φ : P₀ ⋉̂ P₀′) → P /̂ ⋉̂-sym φ /̂ φ ≡ P
   iso» ◻ _ = refl
   iso» [ ν ◻ ] (νν-swapₗ P) = refl
   iso» [ ν [ ν P′ ] ] (νν-swapₗ P) = cong (λ P → [ ν [ ν P ] ]) (swap̃-inv₁ P′)
   iso» [ ν ◻ ] (νν-swapᵣ P) = refl
   iso» [ ν [ ν P′ ] ] (νν-swapᵣ P) = cong (λ P → [ ν [ ν P ] ]) (swap̃-inv₂ P′)
   iso» [ P ➕ Q ] (φ ➕₁ refl) = cong₂ (λ P Q → [ P ➕ Q ]) (iso» P φ) refl
   iso» [ P ➕ Q ] (refl ➕₂ ψ) = cong₂ (λ P Q → [ P ➕ Q ]) refl (iso» Q ψ)
   iso» [ P │ Q ] (φ │₁ refl) = cong₂ (λ P Q → [ P │ Q ]) (iso» P φ) refl
   iso» [ P │ Q ] (refl │₂ ψ) = cong₂ (λ P Q → [ P │ Q ]) refl (iso» Q ψ)
   iso» [ ! P ] (! φ) = cong (λ P → [ ! P ]) (iso» P φ)
   -- Many ν cases, dealing explicitly with cases left implicit in the definition.
   iso» [ ν ◻ ] (ν _) = refl
   iso» [ ν [ ν ◻ ] ] (ν νν-swapₗ P) = refl
   iso» [ ν [ ν [ ν P ] ] ] (ν νν-swapₗ _) = cong (λ P → [ ν [ ν [ ν P ] ] ]) (swap̃-inv₁ P)
   iso» [ ν [ ν ◻ ] ] (ν νν-swapᵣ P) = refl
   iso» [ ν [ ν [ ν P ] ] ] (ν νν-swapᵣ _) = cong (λ P → [ ν [ ν [ ν P ] ] ]) (swap̃-inv₂ P)
   iso» [ ν [ P ➕ Q ] ] (ν (φ ➕₁ refl)) = cong₂ (λ P Q → [ ν [ P ➕ Q ] ]) (iso» P φ) refl
   iso» [ ν [ P ➕ Q ] ] (ν (refl ➕₂ ψ)) = cong₂ (λ P Q → [ ν [ P ➕ Q ] ]) refl (iso» Q ψ)
   iso» [ ν [ P │ Q ] ] (ν (φ │₁ refl)) = cong₂ (λ P Q → [ ν [ P │ Q ] ]) (iso» P φ) refl
   iso» [ ν [ P │ Q ] ] (ν (refl │₂ ψ)) = cong₂ (λ P Q → [ ν [ P │ Q ] ]) refl (iso» Q ψ)
   iso» [ ν [ ν ◻ ] ] (ν (ν φ)) = refl
   iso» [ ν [ ν [ P ➕ Q ] ] ] (ν (ν (φ ➕₁ refl))) = cong₂ (λ P Q → [ ν [ ν [ P ➕ Q ] ] ]) (iso» P φ) refl
   iso» [ ν [ ν [ P ➕ Q ] ] ] (ν (ν (refl ➕₂ ψ))) = cong₂ (λ P Q → [ ν [ ν [ P ➕ Q ] ] ]) refl (iso» Q ψ)
   iso» [ ν [ ν [ P │ Q ] ] ] (ν (ν (φ │₁ refl))) = cong₂ (λ P Q → [ ν [ ν [ P │ Q ] ] ]) (iso» P φ) refl
   iso» [ ν [ ν [ P │ Q ] ] ] (ν (ν (refl │₂ ψ))) = cong₂ (λ P Q → [ ν [ ν [ P │ Q ] ] ]) refl (iso» Q ψ)
   iso» [ ν [ ν [ ν P ] ] ] (ν (ν (ν φ))) = cong (λ P → [ ν P ]) (iso» [ ν [ ν P ] ] (ν (ν φ)))
   iso» [ ν [ ν [ ! P ] ] ] (ν (ν (! φ))) = cong (λ P → [ ν [ ν [ ! P ] ] ]) (iso» P φ)
   iso» [ ν [ ! P ] ] (ν (! φ)) = cong (λ P → [ ν [ ! P ] ]) (iso» P φ)
   -- The next two cases discombobulate the termination-checker.
   iso» [ ν [ ν [ ν P ] ] ] (ν (ν νν-swapₗ _)) = cong (λ P → [ ν P ]) (iso» [ ν [ ν P ] ] (ν νν-swapₗ _))
   iso» [ ν [ ν [ ν P ] ] ] (ν (ν νν-swapᵣ _)) = cong (λ P → [ ν P ]) (iso» [ ν [ ν P ] ] (ν νν-swapᵣ _))

   «iso : ∀ {Γ} {P₀ P₀′ : Proc Γ} (P : ↓ P₀) (φ : P₀ ⋉̂ P₀′) → P /̂ φ /̂ ⋉̂-sym φ ≡ P
   «iso P φ with iso» P (⋉̂-sym φ); ... | iso rewrite ⋉̂-sym-involutive φ = iso

   gc : ∀ {Γ} {P₀ P₀′ : Proc Γ} (φ : P₀ ⋉̂ P₀′) → GaloisConnection (poset {a = P₀}) (poset {a = P₀′})
   gc φ = ⟪ flip _/̂_ φ , flip _/̂_ (⋉̂-sym φ) ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ flip _/ᴹ_ φ ∘ᶠ ≤ᴸ⇒≤;
               g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ flip _/ᴹ_ (⋉̂-sym φ) ∘ᶠ ≤ᴸ⇒≤;
               g∘f≤id = λ P → ≤⇒≤ᴸ (≤-reflexive («iso P φ));
               id≤f∘g = λ P → ≤⇒≤ᴸ (≤-reflexive (sym (iso» P φ)))
            }
