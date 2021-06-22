module 747Quantifiers where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s) -- added ≤
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) -- added proj₂
open import Data.Sum using (_⊎_; inj₁; inj₂ ) -- added inj₁, inj₂
open import Function using (_∘_) -- added

-- Copied from 747Isomorphism.

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  constructor mk-≃  -- This has been added, not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- Logical forall is, not surpringly, ∀.
-- Forall elimination is also function application.

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- In fact, A → B is nicer syntax for ∀ (_ : A) → B.

-- 747/PLFA exercise: ForAllDistProd (1 point)
-- Show that ∀ distributes over ×.
-- (The special case of → distributes over × was shown in the Connectives chapter.)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ →× → ⟨ proj₁ ∘ →× , proj₂ ∘ →× ⟩
    ; from = λ →×→ a → ⟨ proj₁ →×→ a , proj₂ →×→ a ⟩
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

-- 747/PLFA exercise: SumForAllImpForAllSum (1 point)
-- Show that a disjunction of foralls implies a forall of disjunctions.

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ →b) a = inj₁ (→b a)
⊎∀-implies-∀⊎ (inj₂ →c) a = inj₂ (→c a)

-- Existential quantification can be defined as a pair:
-- a witness and a proof that the witness satisfies the property.

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- Some convenient syntax.

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Unfortunately, we can use the RHS syntax in code,
-- but the LHS will show up in displays of goal and context.

-- This is equivalent to defining a dependent record type.

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- By convention, the library uses ∃ when the domain of the bound variable is implicit.

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

-- More special syntax.

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Above we saw two ways of constructing an existential.
-- We eliminate an existential with a function that consumes the
-- witness and proof and reaches a conclusion C.

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , x₁ ⟩ = f x x₁

-- This is a generalization of currying (from Connectives).
-- currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- 747/PLFA exercise: ExistsDistSum (2 points)
-- Show that existentials distribute over disjunction.

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ {A} {B} {C} = record
  { to = front
  ; from = back
  ; from∘to = λ { ⟨ _ , inj₁ _ ⟩ → refl ; ⟨ _ , inj₂ _ ⟩ → refl}
  ; to∘from = λ { (inj₁ ⟨ _ , _ ⟩) → refl ; (inj₂ ⟨ _ , _ ⟩) → refl}
  }
 where
   front : ∃[ x ] (B x ⊎ C x) → ∃[ x ] B x ⊎ ∃[ x ] C x
   front ⟨ a , inj₁ x ⟩ = inj₁ ⟨ a , x ⟩
   front ⟨ a , inj₂ y ⟩ = inj₂ ⟨ a , y ⟩
   back : ∃[ x ] B x ⊎ ∃[ x ] C x → ∃[ x ] (B x ⊎ C x)
   back (inj₁ ⟨ x , y ⟩) = ⟨ x , inj₁ y ⟩
   back (inj₂ ⟨ x , y ⟩) = ⟨ x , inj₂ y ⟩

-- 747/PLFA exercise: ExistsProdImpProdExists (1 point)
-- Show that existentials distribute over ×.

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ fst , snd ⟩ ⟩ = ⟨ ⟨ a , fst ⟩ , ⟨ a , snd ⟩ ⟩

-- An existential example: revisiting even/odd.

-- Recall the mutually-recursive definitions of even and odd.

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- An number is even iff it is double some other number.
-- A number is odd iff is one plus double some other number.
-- Proofs below.

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc x) with odd-∃ x
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc x) with even-∃ x
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ =  even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

-- PLFA exercise: what if we write the arithmetic more "naturally"?
-- (Proof gets harder but is still doable).

-- 747/PLFA exercise: AltLE (3 points)
-- An alternate definition of y ≤ z.
-- (Optional exercise: Is this an isomorphism?)

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n

≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) rewrite +-identityʳ m = refl

+-identityᴸ : ∀ (m : ℕ) → zero + m ≡ m
+-identityᴸ m = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

suc-either-way : ∀ (m n : ℕ) → m + suc n ≡ suc m + n
suc-either-way zero n = refl
suc-either-way (suc m) n rewrite +-suc m n = refl

+1-suc : ∀ (m : ℕ) → suc m ≡ m + 1
+1-suc zero = refl
+1-suc (suc m) rewrite +1-suc m = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n rewrite +-suc n m | +-comm m n = refl

suc-comm : ∀ (m n : ℕ) → suc (m + n) ≡ n + suc m
suc-comm zero zero = refl
suc-comm zero (suc n) rewrite +1-suc n = refl
suc-comm (suc m) n rewrite +-comm n (suc (suc m)) = refl

+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m + p ≤ m + q

+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

∃-≤ : ∀ {y z : ℕ} → ( (y ≤ z) ⇔ ( ∃[ x ] (y + x ≡ z) ) )
∃-≤ {y} {z} = record
  { to = g
  ; from = f
  }
 where
  g : ∀ { m n : ℕ } → (m ≤ n) → (∃[ x ] ( x + m ≡ n))
  g {m} {n} z≤n rewrite sym (+-identityʳ n) = ⟨ n , refl ⟩
  g (s≤s {m} {n} m≤n) = ?
  f : _
  f ⟨ zero , refl ⟩ rewrite +-identityʳ y = ≤-refl
  f ⟨ suc x , refl ⟩ = +-monoˡ-≤  0 (suc x) y z≤n

-- The negation of an existential is isomorphic to a universal of a negation.

open import Data.Empty using (⊥-elim)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to = λ ¬∃B a Ba → ¬∃B ⟨ a , Ba ⟩
    ; from = λ{∀¬B ⟨ a , Ba ⟩ → ∀¬B a Ba}
    ; from∘to = λ ¬∃B → extensionality (⊥-elim ∘ ¬∃B)
    ; to∘from = λ ∀¬B → refl
    }

-- 747/PLFA exercise: ExistsNegImpNegForAll (1 point)
-- Existence of negation implies negation of universal.

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬Ba ⟩ ∀B = ¬Ba (∀B a)

-- The converse cannot be proved in intuitionistic logic.

-- PLFA exercise: isomorphism between naturals and existence of canonical binary.
-- This is essentially what we did at the end of 747Isomorphism.
