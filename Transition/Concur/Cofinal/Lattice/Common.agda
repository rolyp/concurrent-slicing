module Transition.Concur.Cofinal.Lattice.Common where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; inc) public;
      open ᴬ.Action public; open ᴬ.Actionᵇ public; open ᴬ.Actionᶜ public
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬ⌣-sym; ᴬ⌣-sym-involutive; ᴬγ) public;
      open _ᴬ⌣_ public
   open import Action.Concur.Lattice using (residual) public
   open import Action.Lattice as ᴬ̃ using () public;
      open ᴬ̃.↓_ public; open ᴬ̃.↓⁻_ public; open ᴬ̃.↓ᵇ_ public; open ᴬ̃.↓ᶜ_ public
   open import Action.Ren.Lattice using () renaming (_* to _ᴬ*̃) public
   open import Braiding.Proc using (module _⋉̂_) public;
      open _⋉̂_ public
   open import Braiding.Proc.Lattice using (braid̂) public
   open import Lattice using (Lattices) public;
      open Lattice.Prefixes ⦃...⦄ public
   open import Name as ᴺ using (Name; Cxt; _+_) public
   open import Name.Lattice as ᴺ̃ using (zero) public;
      open ᴺ̃.↓_ public
   open import Proc as ᴾ using (Proc; Proc↱; Proc↲) public;
      open ᴾ.Proc public
   open import Proc.Lattice as ᴾ̃ using () public;
      open ᴾ̃.↓_ public; open ᴾ̃.↓⁻_ public
   open import Proc.Ren.Lattice using () renaming (_* to _*̃) public
   open import Ren as ᴿ using () public;
      open ᴿ.Renameable ⦃...⦄ public
   open import Ren.Lattice as ᴿ̃ using (_̃_; swap; pop; push; id; repl; weaken; _ᴿ+_; suc) public
   open import Ren.Lattice.Properties public
   open import Ren.Properties public
   open import Transition as ᵀ using (_—[_-_]→_) public;
      open ᵀ._—[_-_]→_ public
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁) public;
      open Concur₁ public
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁) public
   open import Transition.Lattice using (tgt; action; step⁻; step) public
   open import Transition.Ren using (_*ᵇ; _*ᶜ) public
   open import Transition.Ren.Lattice using (renᵇ-tgt-comm; renᵇ-action-comm; renᶜ-tgt-comm; renᶜ-action-comm) public

   open Delta′ public

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) → ↓ P → ↓ P′
   braiding ˣ∇ˣ eq rewrite eq = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂

   ◻≢[-] : ∀ {Γ} {a : Action Γ} {a′ : ↓⁻ a} → _≡_ {A = ↓_ {A = Action Γ} a} ◻ [ a′ ] → ⊥
   ◻≢[-] ()

   [•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] : ∀ {Γ} {x y : Name Γ} →
                        _≡_ {A = ↓_ {A = Action Γ} (• x 〈 y 〉 ᶜ)} [ • x 〈 ◻ 〉 ᶜ ] [ • x 〈 [ y ] 〉 ᶜ ] → ⊥
   [•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] ()

   [•x〈-〉ᶜ]-inj : ∀ {Γ} {x y : Name Γ} {y′ y″ : ↓ y} →
                 _≡_ {A = ↓_ {A = Action Γ} (• x 〈 y 〉 ᶜ)} [ • x 〈 y′ 〉 ᶜ ] [ • x 〈 y″ 〉 ᶜ ] → y′ ≡ y″
   [•x〈-〉ᶜ]-inj {y′ = y′} {.y′} refl = refl

   [•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] : ∀ {Γ} {x : Name Γ} →
                           _≡_ {A = ↓_ {A = Action Γ} ((• x) ᵇ)} [ • x ﹙ ◻ ﹚ ᵇ ] [ • x ﹙ [ ᴺ.zero ] ﹚ ᵇ ] → ⊥
   [•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] ()

   [•x﹙-﹚ᵇ]-inj : ∀ {Γ} {x : Name Γ} {y′ y″ : ↓ ᴺ.zero} →
                 _≡_ {A = ↓_ {A = Action Γ} ((• x) ᵇ)} [ • x ﹙ y′ ﹚ ᵇ ] [ • x ﹙ y″ ﹚ ᵇ ] → y′ ≡ y″
   [•x﹙-﹚ᵇ]-inj {y′ = y′} {.y′} refl = refl

   -- Helpers arise from need to pattern-match on an equality to get braiding to reduce.
   reduce-ˣ∇ˣ : ∀ {Γ P P′} {x u : Name Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ˣ∇ˣ {x = x} {u}) {0} γ P† ≅ P†
   reduce-ˣ∇ˣ refl _ = ≅-refl

   reduce-ᵇ∇ᵇ : ∀ {Γ P P′} {a a′ : Actionᵇ Γ} (γ : ((ᴿ.swap ᴿ.ᴿ+ 0) *) P ≡ P′) (P† : ↓ P) →
                braiding (ᵇ∇ᵇ {a = a} {a′}) {0} γ P† ≅ ((swap ᴿ+ 0) *̃) P†
   reduce-ᵇ∇ᵇ refl _ = ≅-refl

   reduce-ᵇ∇ᶜ : ∀ {Γ P P′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᵇ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᵇ∇ᶜ refl _ = ≅-refl

   reduce-ᶜ∇ᵇ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᶜ∇ᵇ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᶜ∇ᵇ refl _ = ≅-refl

   reduce-ᶜ∇ᶜ : ∀ {Γ P P′} {a : Actionᶜ Γ} {a′ : Actionᶜ Γ} (γ : P ≡ P′) (P† : ↓ P) →
                braiding (ᶜ∇ᶜ {a = a} {a′}) {0} γ P† ≅ P†
   reduce-ᶜ∇ᶜ refl _ = ≅-refl

   ◻-cong : ∀ {Γ} {P₀ P₁ : Proc Γ} → P₀ ≡ P₁ →
            _≅_ {A = ↓_ {A = Proc Γ} _} (◻ {P = P₀}) {↓_ {A = Proc Γ} _} (◻ {P = P₁})
   ◻-cong refl = ≅-refl

   [-│]-cong : ∀ {Γ} {P₀ P₁ Q₀ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₁} (Q : ↓ Q₀) → P₀ ≡ P₁ → P ≅ P′ →
               _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P′ │ Q ]
   [-│]-cong _ refl ≅-refl = ≅-refl

   [│-]-cong : ∀ {Γ} {P₀ Q₀ Q₁ : Proc Γ} (P : ↓ P₀) {Q : ↓ Q₀} {Q′ : ↓ Q₁} → Q₀ ≡ Q₁ → Q ≅ Q′ →
               _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P │ Q′ ]
   [│-]-cong _ refl ≅-refl = ≅-refl

   [-│-]-cong : ∀ {Γ} {P₀ P₁ Q₀ Q₁ : Proc Γ} {P : ↓ P₀} {P′ : ↓ P₁} {Q : ↓ Q₀} {Q′ : ↓ Q₁} →
                P₀ ≡ P₁ → P ≅ P′ → Q₀ ≡ Q₁ → Q ≅ Q′ →
                _≅_ {A = ↓_ {A = Proc Γ} _} [ P │ Q ] {↓_ {A = Proc Γ} _} [ P′ │ Q′ ]
   [-│-]-cong refl ≅-refl refl ≅-refl = ≅-refl

   [ν-]-cong : ∀ {Γ} {P₀ P₁ : Proc (Γ + 1)} {P : ↓ P₀} {P′ : ↓ P₁} → P₀ ≡ P₁ → P ≅ P′ →
               _≅_ {A = ↓_ {A = Proc Γ} _} [ ν P ] {↓_ {A = Proc Γ} _} [ ν P′ ]
   [ν-]-cong refl ≅-refl = ≅-refl

   coerceAction : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) → ↓ π₂ (ᴬ⊖ (ᴬ⌣-sym 𝑎)) → ↓ π₁ (ᴬ⊖ 𝑎)
   coerceAction 𝑎 rewrite sym (ᴬγ 𝑎) | ᴬ⌣-sym-involutive 𝑎 = idᶠ

   postulate
      ᴬgamma₁ :
         ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
         action (E′/E (⊖₁ 𝐸)) (tgt E P′) ≡ coerceAction 𝑎 (residual (ᴬ⌣-sym 𝑎) (action E′ P′))
         ×
         action (E/E′ (⊖₁ 𝐸)) (tgt E′ P′) ≡ residual 𝑎 (action E P′)

   module ≡action
      {Γ} {x y u z : Name Γ} {P₀ R₀ R′₀} {E : P₀ —[ • x 〈 y 〉 ᶜ - _ ]→ R₀} {E′ : P₀ —[ • u 〈 z 〉 ᶜ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)  where

      module _
         (R : ↓ R₀) (≡R : tgt E P ≡ R) where

         ≡a′/a : action (E′/E (⊖₁ 𝐸)) R ≡ action E′ P
         ≡a′/a = trans (cong (action (E′/E (⊖₁ 𝐸))) (sym ≡R)) (π₁ (ᴬgamma₁ 𝐸 P))

         z₁≡z₂ : (z₁ z₂ : ↓ z)
                 (α : (z₁ ≡ ◻ × action E′ P ≡ ◻ → ⊥) → action E′ P ≡ [ • u 〈 z₁ 〉 ᶜ ])
                 (β : (z₂ ≡ ◻ × action (E′/E (⊖₁ 𝐸)) R ≡ ◻ → ⊥) → action (E′/E (⊖₁ 𝐸)) R ≡ [ • u 〈 z₂ 〉 ᶜ ]) →
                 z₁ ≡ z₂
         z₁≡z₂ ◻ ◻ _ _ = refl
         z₁≡z₂ [ .z ] [ .z ] _ _ = refl
         z₁≡z₂ ◻ [ .z ] α β rewrite ≡a′/a =
            let δ : action E′ P ≡ [ • u 〈 [ z ] 〉 ᶜ ]
                δ = β (λ { (() , _) })
            in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
         z₁≡z₂ [ .z ] ◻ α β rewrite sym ≡a′/a =
            let δ : action (E′/E (⊖₁ 𝐸)) R ≡ [ • u 〈 [ z ] 〉 ᶜ ]
                δ = α (λ { (() , _) })
            in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

      module _
         (R′ : ↓ R′₀) (≡R′ : tgt E′ P ≡ R′) where

         ≡a/a′ : action (E/E′ (⊖₁ 𝐸)) R′ ≡ action E P
         ≡a/a′ = trans (cong (action (E/E′ (⊖₁ 𝐸))) (sym ≡R′)) (π₂ (ᴬgamma₁ 𝐸 P))

         y₁≡y₂ : (y₁ y₂ : ↓ y)
                 (α : (y₁ ≡ ◻ × action E P ≡ ◻ → ⊥) → action E P ≡ [ • x 〈 y₁ 〉 ᶜ ])
                 (β : (y₂ ≡ ◻ × action (E/E′ (⊖₁ 𝐸)) R′ ≡ ◻ → ⊥) → action (E/E′ (⊖₁ 𝐸)) R′ ≡ [ • x 〈 y₂ 〉 ᶜ ]) →
                 y₁ ≡ y₂
         y₁≡y₂ ◻ ◻ _ _ = refl
         y₁≡y₂ [ .y ] [ .y ] _ _ = refl
         y₁≡y₂ ◻ [ .y ] α β rewrite ≡a/a′ =
            let δ : action E P ≡ [ • x 〈 [ y ] 〉 ᶜ ]
                δ = β (λ { (() , _) })
            in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
         y₁≡y₂ [ .y ] ◻ α β rewrite sym ≡a/a′ =
            let δ : action (E/E′ (⊖₁ 𝐸)) R′ ≡ [ • x 〈 [ y ] 〉 ᶜ ]
                δ = α (λ { (() , _) })
            in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

   module ≡action′
      {Γ} {x y u : Name Γ} {P₀ R₀ R′₀} {E : P₀ —[ • x 〈 y 〉 ᶜ - _ ]→ R₀} {E′ : P₀ —[ (• u ) ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (P : ↓ P₀)  where

      module _
         (R : ↓ R₀) (≡R : tgt E P ≡ R) where

         ≡a′/a : action (E′/E (⊖₁ 𝐸)) R ≡ action E′ P
         ≡a′/a = trans (cong (action (E′/E (⊖₁ 𝐸))) (sym ≡R)) (π₁ (ᴬgamma₁ 𝐸 P))

         z₁≡z₂ : (z₁ z₂ : ↓ ᴺ.zero)
                 (α : (z₁ ≡ ◻ × action E′ P ≡ ◻ → ⊥) → action E′ P ≡ [ • u ﹙ z₁ ﹚ ᵇ ])
                 (β : (z₂ ≡ ◻ × action (E′/E (⊖₁ 𝐸)) R ≡ ◻ → ⊥) → action (E′/E (⊖₁ 𝐸)) R ≡ [ • u ﹙ z₂ ﹚ ᵇ ]) →
                 z₁ ≡ z₂
         z₁≡z₂ ◻ ◻ _ _ = refl
         z₁≡z₂ [ .ᴺ.zero ] [ .ᴺ.zero ] _ _ = refl
         z₁≡z₂ ◻ [ .ᴺ.zero ] α β rewrite ≡a′/a =
            let δ : action E′ P ≡ [ • u ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
                δ = β (λ { (() , _) })
            in ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
         z₁≡z₂ [ .ᴺ.zero ] ◻ α β rewrite sym ≡a′/a =
            let δ : action (E′/E (⊖₁ 𝐸)) R ≡ [ • u ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
                δ = α (λ { (() , _) })
            in ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

      module _
         (R′ : ↓ R′₀) (≡R′ : tgt E′ P ≡ R′) where

         ≡a/a′ : action (E/E′ (⊖₁ 𝐸)) R′ ≡ (push ᴬ*̃) (action E P)
         ≡a/a′ = trans (cong (action (E/E′ (⊖₁ 𝐸))) (sym ≡R′)) (π₂ (ᴬgamma₁ 𝐸 P))

         y₁≡y₂ : (y₁ : ↓ y) (y₂ : ↓ ᴺ.suc y)
                 (α : (y₁ ≡ ◻ × action E P ≡ ◻ → ⊥) → action E P ≡ [ • x 〈 y₁ 〉 ᶜ ])
                 (β : (y₂ ≡ ◻ × action (E/E′ (⊖₁ 𝐸)) R′ ≡ ◻ → ⊥) → action (E/E′ (⊖₁ 𝐸)) R′ ≡ [ • ᴺ.suc x 〈 y₂ 〉 ᶜ ]) →
                 push ̃ y₁ ≡ y₂
         y₁≡y₂ ◻ ◻ _ _ = refl
         y₁≡y₂ [ .y ] [ .(ᴺ.suc y) ] _ _ = refl
         y₁≡y₂ ◻ [ .(ᴺ.suc y) ] α β =
            let δ : action E P ≡ [ • x 〈 [ y ] 〉 ᶜ ]
                δ = let open EqReasoning (setoid _) in
                   begin
                      action E P
                   ≡⟨ {!!} ⟩
                      [ • x 〈 [ y ] 〉 ᶜ ]
                   ∎
            in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
         y₁≡y₂ [ .y ] ◻ α β =
            let δ : action (E/E′ (⊖₁ 𝐸)) R′ ≡ [ • ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ ]
                δ = trans ≡a/a′ (cong (push ᴬ*̃) (α (λ { (() , _) })))
            in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
