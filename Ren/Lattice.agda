module Ren.Lattice where

   open import ConcurrentSlicingCommon hiding (preorder; poset)
   import Relation.Binary.PreorderReasoning as PreorderReasoning

   import Ext.Algebra.Properties.Lattice
   open import Ext.Algebra

   open import Lattice using (Lattices; module Lattices; Prefixes; module Prefixes);
      open Prefixes ⦃...⦄ using (ᴹ; poset) renaming (
            ↓_ to ↓′_; _≤_ to _≤′_; _⊔_ to _⊔′_; _⊓_ to _⊓′_; ≤ᴸ⇒≤ to ≤′ᴸ⇒≤′; ≤⇒≤ᴸ to ≤′⇒≤′ᴸ; isLattice to isLattice′
         )
   open import Name as ᴺ using (Name; _≟_)
   open import Name.Lattice as ᴺ̃ using ([_]; zero)
   open import Ren as ᴿ using (Ren); open ᴿ.Renameable ⦃...⦄ renaming (_* to _*′; *-preserves-≃ₑ to *′-preserves-≃ₑ)

   ↓_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Set
   ↓_ {Γ} ρ = (x : Name Γ) → ↓′ (ρ x)

   -- Lift ≤ pointwise to renaming-slices.
   infix 4 _≤_
   _≤_ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} (ρ ρ′ : ↓ ρ₀) → Set
   ρ ≤ ρ′ = ∀ x → ρ x ≤′ ρ′ x

   -- Least prefix of ρ.
   ◻ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → ↓ ρ
   ◻ x = ᴺ̃.◻

   ◻≤ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {ρ : ↓ ρ₀} → ◻ ≤ ρ
   ◻≤ x = ᴺ̃.◻

   to-↓ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ↓ ρ
   to-↓ ρ x = ᴺ̃.to-↓ (ρ x)

   to-↓-preserves-≃ₑ : ∀ {Γ Γ′} {ρ ρ′ : Ren Γ Γ′} → ρ ≃ₑ ρ′ → ∀ x → to-↓ ρ x ≅ to-↓ ρ′ x
   to-↓-preserves-≃ₑ ρ = (≅-cong ᴺ̃.to-↓) ∘ᶠ ≡-to-≅ ∘ᶠ ρ

   top : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) {ρ′ : ↓ ρ} → ρ′ ≤ to-↓ ρ
   top ρ {ρ′} x with ρ′ x
   ... | ᴺ̃.◻ = ᴺ̃.◻
   ... | [ .(ρ x) ] = [ ρ x ]

   infixr 8 _*
   _* : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {x : Name Γ} → ↓ ρ → ↓′ x → ↓′ (ρ *′) x
   (ρ *) ᴺ̃.◻ = ᴺ̃.◻
   (ρ *) [ x ] = ρ x

   _*ᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {ρ ρ′ : ↓ ρ₀} {x₀ : Name Γ} {x x′ : ↓′ x₀} → ρ ≤ ρ′ → x ≤′ x′ → (ρ *) x ≤′ (ρ′ *) x′
   (ρ *ᴹ) ᴺ̃.◻ = ᴺ̃.◻
   (ρ *ᴹ) [ x ] = ρ x

   -- TODO: fix the syntax here; ρ can no longer usefully be implicit.
   _↦_ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} (x : Name Γ) → ↓′ (ρ *′) x → ↓ ρ
   _↦_ _ ᴺ̃.◻ = ◻
   _↦_ x [ ._ ] u with x ≟ u
   _↦_ {ρ = ρ} x [ ._ ] .x | yes refl = [ ρ x ]
   ... | no _ = ᴺ̃.◻

   _↦ᴹ_ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} (x : Name Γ) {u u′ : ↓′ (ρ *′) x} → u ≤′ u′ → _↦_ {ρ = ρ} x u ≤ x ↦ u′
   _↦ᴹ_ _ ᴺ̃.◻ _ = ᴺ̃.◻
   _↦ᴹ_ x [ ._ ] u with x ≟ u
   _↦ᴹ_ {ρ = ρ} x [ ._ ] .x | yes refl = [ ρ x ]
   _↦ᴹ_ x [ ._ ] u | no _ = ᴺ̃.◻

   _⁻¹[_]_ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ↓′ (ρ *′) x → ↓′ x
   _ ⁻¹[ _ ] ᴺ̃.◻ = ᴺ̃.◻
   _ ⁻¹[ x ] [ ._ ] = [ x ]

   _⁻¹ᴹ[_]_ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) {u u′ : ↓′ (ρ *′) x} → u ≤′ u′ → ρ ⁻¹[ x ] u ≤′ ρ ⁻¹[ x ] u′
   _ ⁻¹ᴹ[ _ ] ᴺ̃.◻ = ᴺ̃.◻
   _ ⁻¹ᴹ[ x ] [ ._ ] = [ x ]

   -- Uncurried version of * convenient for the Galois connection.
   get : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {x : Name Γ} → ↓ ρ × ↓′ x → ↓′ (ρ *′) x
   get {ρ = ρ} {x} = uncurry (_* {ρ = ρ} {x = x})

   postulate
      getᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {ρ ρ′ : ↓ ρ₀} {x₀ : Name Γ} {x x′ : ↓′ x₀} → ρ ≤ ρ′ × x ≤′ x′ → get (ρ , x) ≤′ get (ρ′ , x′)

   -- Lower adjoint of get.
   put : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ↓′ (ρ *′) x → ↓ ρ × ↓′ x
   put ρ x u = x ↦ u , ρ ⁻¹[ x ] u

   putᴹ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) {u u′ : ↓′ (ρ *′) x} → u ≤′ u′ →
          let ρ′ , x′ = put ρ x u; ρ″ , x″ = put ρ x u′ in ρ′ ≤ ρ″ × x′ ≤′ x″
   putᴹ ρ x u = x ↦ᴹ u , ρ ⁻¹ᴹ[ x ] u

   suc : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → ↓ ρ → ↓ ᴿ.suc ρ
   suc _ ᴺ.zero = ᴺ̃.zero
   suc ρ (ᴺ.suc x) = ᴺ̃.suc (ρ x)

   suc-preserves-≃ₑ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {ρ σ : ↓ ρ₀} → ρ ≃ₑ σ → suc ρ ≃ₑ suc σ
   suc-preserves-≃ₑ _ ᴺ.zero = refl
   suc-preserves-≃ₑ ρ (ᴺ.suc x) = cong ᴺ̃.suc (ρ x)

   sucᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {ρ ρ′ : ↓ ρ₀} → ρ ≤ ρ′ → suc ρ ≤ suc ρ′
   sucᴹ _ ᴺ.zero = [ ᴺ.zero ]
   sucᴹ ρ (ᴺ.suc x) = ᴺ̃.sucᴹ (ρ x)

   pre : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} → ↓ ᴿ.suc ρ₀ → ↓ ρ₀
   pre {ρ₀ = ρ₀} ρ x with ρ (ᴺ.suc x)
   ... | ᴺ̃.◻ = ᴺ̃.◻
   ... | [ .(ᴺ.suc (ρ₀ x)) ] = [ ρ₀ x ]

   preᴹ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {ρ ρ′ : ↓ ᴿ.suc ρ₀} → ρ ≤ ρ′ → pre ρ ≤ pre ρ′
   preᴹ {ρ = ρ} {ρ′} ρ† x with ρ (ᴺ.suc x) | ρ′ (ᴺ.suc x) | ρ† (ᴺ.suc x)
   preᴹ ρ† x | ᴺ̃.◻ | _ | _ = ᴺ̃.◻
   preᴹ ρ† x | [ ._ ] | ᴺ̃.◻ | ()
   preᴹ {ρ₀ = ρ₀} ρ† x | [ ._ ] | [ ._ ] | [ ._ ] = [ ρ₀ x ]

   infixl 6 _ᴿ+_
   _ᴿ+_ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → ↓ ρ → ∀ n → ↓ (ρ ᴿ.ᴿ+ n)
   ρ ᴿ+ ᴺ.zero = ρ
   ρ ᴿ+ (ᴺ.suc n) = suc (ρ ᴿ+ n)

   to-↓-preserves-+ : ∀ {Γ Γ′} Δ (ρ : Ren Γ Γ′) → to-↓ (ρ ᴿ.ᴿ+ Δ) ≃ₑ to-↓ ρ ᴿ+ Δ
   to-↓-preserves-+ ᴺ.zero ρ _ = refl
   to-↓-preserves-+ (ᴺ.suc Δ) ρ ᴺ.zero = refl
   to-↓-preserves-+ (ᴺ.suc Δ) ρ (ᴺ.suc x) rewrite sym (to-↓-preserves-+ Δ ρ x) = refl

   infixr 6 _⊔_
   _⊔_ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} (ρ ρ′ : ↓ ρ₀) → ↓ ρ₀
   (ρ ⊔ ρ′) x = ρ x ⊔′ ρ′ x

   -- Compatible meet.
   infixr 7 _⊓_
   _⊓_ : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} (ρ ρ′ : ↓ ρ₀) → ↓ ρ₀
   (ρ ⊓ ρ′) x = ρ x ⊓′ ρ′ x

   ⊓-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → Commutative _≃ₑ_ (_⊓_ {ρ₀ = ρ})
   ⊓-comm ρ ρ′ x = ᴺ̃.⊓-comm (ρ x) (ρ′ x)

   ⊔-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → Commutative _≃ₑ_ (_⊔_ {ρ₀ = ρ})
   ⊔-comm ρ ρ′ x = ᴺ̃.⊔-comm (ρ x) (ρ′ x)

   ⊓-assoc : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → Associative _≃ₑ_ (_⊓_ {ρ₀ = ρ})
   ⊓-assoc ρ₁ ρ₂ ρ₃ x = ᴺ̃.⊓-assoc (ρ₁ x) (ρ₂ x) (ρ₃ x)

   ⊔-assoc : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → Associative _≃ₑ_ (_⊔_ {ρ₀ = ρ})
   ⊔-assoc ρ₁ ρ₂ ρ₃ x = ᴺ̃.⊔-assoc (ρ₁ x) (ρ₂ x) (ρ₃ x)

   ⊔-absorbs-⊓ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → _Absorbs_ _≃ₑ_ (_⊔_ {ρ₀ = ρ}) _⊓_
   ⊔-absorbs-⊓ ρ ρ′ x = ᴺ̃.⊔-absorbs-⊓ (ρ x) (ρ′ x)

   ⊓-absorbs-⊔ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → _Absorbs_ _≃ₑ_ (_⊓_ {ρ₀ = ρ}) _⊔_
   ⊓-absorbs-⊔ ρ ρ′ x = ᴺ̃.⊓-absorbs-⊔ (ρ x) (ρ′ x)

   isLattice : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → IsLattice _≃ₑ_ (_⊔_ {ρ₀ = ρ}) _⊓_
   isLattice = record {
         isEquivalence = ≃ₑ-equiv;
         ∨-comm = ⊔-comm;
         ∨-assoc = ⊔-assoc;
         ∨-cong = λ ρ ρ′ x → cong₂ _⊔′_ (ρ x) (ρ′ x);
         ∧-comm = ⊓-comm;
         ∧-assoc = ⊓-assoc;
         ∧-cong = λ ρ ρ′ x → cong₂ _⊓′_ (ρ x) (ρ′ x);
         absorptive = ⊔-absorbs-⊓ , ⊓-absorbs-⊔
      }

   private
      lattices : ∀ {Γ Γ′} → Lattices (Ren Γ Γ′)
      lattices = record {
            ↓_ = ↓_; ↓⁻_ = ↓_; _⊔⁻_ = _⊔_; _⊔_ = _⊔_; _⊓⁻_ = _⊓_; _⊓_ = _⊓_;
            isLattice = isLattice; isLattice⁻ = isLattice
         }

   open Lattices using (_≤ᴸ_)

   -- Partial order induced by ⊓ agrees with our extensional definition.
   ≤ᴸ⇒≤ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → _≤ᴸ_ lattices {a = ρ} ⇒ _≤_
   ≤ᴸ⇒≤ ρ = ≤′ᴸ⇒≤′ ∘ᶠ ρ

   ≤⇒≤ᴸ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → _≤_ ⇒ _≤ᴸ_ lattices {a = ρ}
   ≤⇒≤ᴸ ρ = ≤′⇒≤′ᴸ ∘ᶠ ρ

   instance
      prefixes : ∀ {Γ Γ′} → Prefixes (Ren Γ Γ′)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤_; ≤⁻ᴸ⇒≤⁻ = ≤ᴸ⇒≤; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⇒≤ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }

   id : ∀ {Γ} → ↓ (idᶠ {A = Name Γ})
   id = to-↓ idᶠ

   push : ∀ {Γ} → ↓ (ᴿ.push {Γ})
   push = to-↓ ᴿ.push

   pop : ∀ {Γ} {x₀ : Name Γ} (x : ↓′ x₀) → ↓ ᴿ.pop x₀
   pop x ᴺ.zero = x
   pop _ (ᴺ.suc y) = [ y ]

   pop-top : ∀ {Γ} {x₀ : Name Γ} {ρ : ↓ ᴿ.pop x₀} → ρ ≤ pop (ρ ᴺ.zero)
   pop-top {ρ = ρ} ᴺ.zero = ᴹ (ρ ᴺ.zero)
   pop-top {ρ = ρ} (ᴺ.suc x) with ρ (ᴺ.suc x)
   ... | ᴺ̃.◻ = ᴺ̃.◻
   ... | [ .x ] = [ x ]

   popᴹ : ∀ {Γ} {x₀ : Name Γ} {x x′ : ↓′ x₀} → x ≤′ x′ → pop x ≤ pop x′
   popᴹ x ᴺ.zero = x
   popᴹ _ (ᴺ.suc y) = [ y ]

   swap : ∀ {Γ} → ↓ (ᴿ.swap {Γ})
   swap = to-↓ ᴿ.swap
