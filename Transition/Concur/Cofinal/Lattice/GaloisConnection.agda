module Transition.Concur.Cofinal.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⌣-sym); open _ᴬ⌣_
   open import Braiding.Proc using (⋉̂-sym)
   open import Braiding.Proc.Lattice using (braid̂)
   open import Braiding.Proc.Lattice.GaloisConnection using (braid̂ᴹ)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (Cxt; zero; _+_)
   open import Proc as ᴾ using (Proc; Proc↱)
   import Proc.Lattice
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃) using (_*ᴹ)
   open import Ren as ᴿ using (+-preserves-involutivity); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (swap; _ᴿ+_)
   open import Ren.Lattice.Properties
   open import Ren.Properties
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur; ⌣-sym; module Delta′; ⊖); open Delta′
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; ⋈̂-sym)
   open import Transition.Concur.Cofinal.Lattice using (braiding)

   braidingᴹ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P₀ P′₀} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P₀ P′₀) →
               ∀ {P P′ : ↓ P₀} → P ≤ P′ → braiding 𝑎 γ P ≤ braiding 𝑎 γ P′
   braidingᴹ ˣ∇ˣ refl = idᶠ
   braidingᴹ ᵇ∇ᵇ {Δ} refl = ᴹ (swap ᴿ+ Δ) *ᴹ
   braidingᴹ ᵇ∇ᶜ refl = idᶠ
   braidingᴹ ᶜ∇ᵇ refl = idᶠ
   braidingᴹ ᶜ∇ᶜ refl = idᶠ
   braidingᴹ ᵛ∇ᵛ γ = braid̂ᴹ γ

   «iso : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) (P† : ↓ P) →
          braiding 𝑎 (⋈̂-sym 𝑎 Δ γ) (braiding 𝑎 γ P†) ≡ P†
   «iso ˣ∇ˣ refl _ = refl
   «iso {Γ} (ᵇ∇ᵇ {a} {a′}) {Δ} {P} {.(((ᴿ.swap ᴿ.ᴿ+ Δ) *) P)} refl P† =
      let open ≅-Reasoning
          reduce : ∀ (P P′ : Proc (Γ + 2 + Δ)) → ∀ P† →
                   (γ : ((ᴿ.swap ᴿ.ᴿ+ Δ) *) P ≡ P′) → braiding (ᵇ∇ᵇ {a = a} {a′}) {Δ} γ P† ≅ ((swap ᴿ+ Δ) *̃) P†
          reduce = λ { P ._ _ refl → ≅-refl }
      in ≅-to-≡ (
      begin
         braiding ᵇ∇ᵇ {Δ} (⋈̂-sym (ᵇ∇ᵇ {a = a} {a′}) Δ refl) (((swap ᴿ+ Δ) *̃) P†)
      ≅⟨ reduce (((ᴿ.swap ᴿ.ᴿ+ Δ) *) P) P (((swap ᴿ+ Δ) *̃) P†) (⋈̂-sym (ᵇ∇ᵇ {a = a} {a′}) Δ refl) ⟩
         ((swap ᴿ+ Δ) *̃) (((swap ᴿ+ Δ) *̃) P†)
      ≅⟨ swap̃+-involutive Δ P† ⟩
         P†
      ∎)
   «iso ᵇ∇ᶜ refl _ = refl
   «iso ᶜ∇ᵇ refl _ = refl
   «iso ᶜ∇ᶜ refl _ = refl
   «iso ᵛ∇ᵛ = flip Braiding.Proc.Lattice.GaloisConnection.«iso

   iso» : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) (P† : ↓ P′) →
          braiding 𝑎 γ (braiding 𝑎 (⋈̂-sym 𝑎 Δ γ) P†) ≡ P†
   iso» ˣ∇ˣ refl _ = refl
   iso» (ᵇ∇ᵇ {a} {a′}) {Δ} refl P† =
      let open ≅-Reasoning
      in ≅-to-≡ (
      begin
         ((swap ᴿ+ Δ) *̃) (braiding ᵇ∇ᵇ {Δ} (⋈̂-sym (ᵇ∇ᵇ {a = a} {a′}) Δ refl) P†)
      ≅⟨ {!!} ⟩
         ((swap ᴿ+ Δ) *̃) (((swap ᴿ+ Δ) *̃) P†)
      ≅⟨ swap̃+-involutive Δ P† ⟩
         P†
      ∎)
   iso» ᵇ∇ᶜ refl _ = refl
   iso» ᶜ∇ᵇ refl _ = refl
   iso» ᶜ∇ᶜ refl _ = refl
   iso» ᵛ∇ᵛ = flip Braiding.Proc.Lattice.GaloisConnection.iso»

   gc : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) →
        GaloisConnection (poset {a = P}) (poset {a = P′})
   gc 𝑎 {Δ} γ = ⟪ braiding 𝑎 γ , braiding 𝑎 (⋈̂-sym 𝑎 Δ γ) ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braidingᴹ 𝑎 γ ∘ᶠ ≤ᴸ⇒≤;
               g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ braidingᴹ 𝑎 (⋈̂-sym 𝑎 Δ γ) ∘ᶠ ≤ᴸ⇒≤;
               g∘f≤id = λ P → ≤⇒≤ᴸ (≤-reflexive («iso 𝑎 γ P));
               id≤f∘g = λ P → ≤⇒≤ᴸ (≤-reflexive (sym (iso» 𝑎 γ P)))
            }
