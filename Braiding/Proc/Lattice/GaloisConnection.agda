-- A bound braid gives rise to a lattice isomorphism.
module Braiding.Proc.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset; trans)
   open import Ext.Algebra
   import Relation.Binary.EqReasoning as EqReasoning

   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (_+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (_≤⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (_*ᴹ) renaming (_* to _*̃)
   open import Ren as ᴿ using (swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (to-↓)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Braiding.Proc using (_⋉̂_; module _⋉̂_; ⋉̂-sym; ⋉̂-sym-involutive); open _⋉̂_
   open import Braiding.Proc.Lattice using (braid̂; braid-ν)

   braid̂ᴹ : ∀ {Γ} {P₀ P₀′ : Proc Γ} {P P′ : ↓ P₀} (φ : P₀ ⋉̂ P₀′) → P ≤ P′ → braid̂ φ P ≤ braid̂ φ P′
   braid̂ᴹ _ ◻ = ◻
   braid̂ᴹ {P = [ ν ◻ ]} {[ ν ◻ ]} (νν-swapₗ _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν ◻ ]} {[ ν [ ν _ ] ]} (νν-swapₗ _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {Γ} {P₀ = ν (ν .((swap *) P₀))} {P = [ ν [ ν P ] ]} {[ ν [ ν P′ ] ]} (νν-swapₗ P₀) [ ν [ ν P† ] ] =
        [ ν [ ν substᴹ ((ᴹ ᴿ̃.swap *ᴹ) P†) (swap-involutive P₀) ] ]
   braid̂ᴹ {P = [ ν [ _ ] ]} {[ ν ◻ ]} (νν-swapₗ _) [ ν () ]
   braid̂ᴹ {P = [ ν ◻ ]} {[ ν ◻ ]} (νν-swapᵣ _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν ◻ ]} {[ ν [ ν _ ] ]}(νν-swapᵣ _)  [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {Γ} {P₀ = ν (ν .P₀)} {P = [ ν [ ν P ] ]} {[ ν [ ν P′ ] ]} (νν-swapᵣ P₀) [ ν [ ν P† ] ] =
        [ ν [ ν (ᴹ ᴿ̃.swap *ᴹ) P† ] ]
   braid̂ᴹ {P = [ ν [ _ ] ]} {[ ν ◻ ]} (νν-swapᵣ _) [ ν () ]
   braid̂ᴹ (φ ➕₁ refl) [ P ➕ Q ] = [ braid̂ᴹ φ P ➕ Q ]
   braid̂ᴹ (refl ➕₂ ψ) [ P ➕ Q ] = [ P ➕ braid̂ᴹ ψ Q ]
   braid̂ᴹ (φ │₁ refl) [ P │ Q ] = [ braid̂ᴹ φ P │ Q ]
   braid̂ᴹ (refl │₂ ψ) [ P │ Q ] = [ P │ braid̂ᴹ ψ Q ]
   braid̂ᴹ (! φ) [ ! P ] = [ ! (braid̂ᴹ φ P) ]
   -- For ν, need to be explicit about sub-cases left implicit in the definition.
   braid̂ᴹ {P = [ ν ◻ ]} {[ ν ◻ ]} (ν _) [ ν _ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ Ο ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ _ •∙ _ ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ • _ 〈 _ 〉∙ _ ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ _ ➕ _ ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ _ │ _ ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ ν _ ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν .◻ ]} {[ ν [ ! _ ] ]} (ν _) [ ν ◻ ] = [ ν ◻ ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ Ο ] ] = [ ν (braid̂ᴹ φ [ Ο ]) ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ x •∙ P ] ] = [ ν (braid̂ᴹ φ [ x •∙ P ]) ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ • x 〈 y 〉∙ P ] ] = [ ν (braid̂ᴹ φ [ • x 〈 y 〉∙ P ]) ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ P ➕ Q ] ] = [ ν (braid̂ᴹ φ [ P ➕ Q ]) ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ P │ Q ] ] = [ ν (braid̂ᴹ φ [ P │ Q ]) ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ ν P ] ] = [ ν (braid̂ᴹ φ [ ν P ]) ]
   braid̂ᴹ {P = [ ν ._ ]} {[ ν [ ._ ] ]} (ν φ) [ ν [ ! P ] ] = [ ν (braid̂ᴹ φ [ ! P ]) ]
   braid̂ᴹ {P = [ ν [ _ ] ]} {[ ν ◻ ]} (ν φ) [ ν () ]

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
   iso» : ∀ {Γ} {P₀ P₀′ : Proc Γ} (P : ↓ P₀′) (φ : P₀ ⋉̂ P₀′) → braid̂ φ (braid̂ (⋉̂-sym φ) P) ≡ P
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

   «iso : ∀ {Γ} {P₀ P₀′ : Proc Γ} (P : ↓ P₀) (φ : P₀ ⋉̂ P₀′) → braid̂ (⋉̂-sym φ) (braid̂ φ P) ≡ P
   «iso P φ with iso» P (⋉̂-sym φ); ... | iso rewrite ⋉̂-sym-involutive φ = iso

   gc : ∀ {Γ} {P₀ P₀′ : Proc Γ} (φ : P₀ ⋉̂ P₀′) → GaloisConnection (poset {a = P₀}) (poset {a = P₀′})
   gc φ = ⟪ braid̂ φ , braid̂ (⋉̂-sym φ) ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braid̂ᴹ φ ∘ᶠ ≤ᴸ⇒≤;
               g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braid̂ᴹ (⋉̂-sym φ) ∘ᶠ ≤ᴸ⇒≤;
               g∘f≤id = λ P → ≤⇒≤ᴸ (≤-reflexive («iso P φ));
               id≤f∘g = λ P → ≤⇒≤ᴸ (≤-reflexive (sym (iso» P φ)))
            }
