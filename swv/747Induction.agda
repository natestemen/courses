module 747Induction where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- PLFA coverage of identity, associativity, commutativity, distributivity.

-- An example of the associative law for addition, presented using equational reasoning.

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- A theorem easy to prove.

+-identityᴸ : ∀ (m : ℕ) → zero + m ≡ m
+-identityᴸ m = refl

-- A first nontrivial theorem.
-- An equational proof is shown in PLFA.
-- Instead we will use 'rewrite'.

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) rewrite +-identityʳ m = refl

*-identityᴸ : ∀ (m : ℕ) → zero * m ≡ zero
*-identityᴸ m = refl

*-identityʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-identityʳ zero = refl
*-identityʳ (suc m) = *-identityʳ m

*-idʳ : ∀ (m : ℕ) → m * (suc zero) ≡ m
*-idʳ zero = refl
*-idʳ (suc m) rewrite *-idʳ m = refl

-- PLFA's proof uses helpers cong and sym imported from the standard library,
-- and a form of equational reasoning that allows more elaborate justification than above.
-- We can use cong in place of rewrite.

+-identityʳ′ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ′ zero = refl
+-identityʳ′ (suc m) = cong suc (+-identityʳ′ m)

-- Associativity of addition.
-- (Done first in PLFA.)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

-- A useful lemma about addition.
-- Equational proof shown in PLFA.

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

-- Commutativity of addition.
-- Equational proof shown in PLFA.

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n rewrite +-suc n m | +-comm m n = refl

-- 747/PLFA exercise: AddSwap (1 point)
-- Please do this without using induction/recursion.

+-swap : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-comm m n | +-suc n (m + p) | +-assoc n m p = refl

+-swap-suc : ∀ (m n p : ℕ) → suc (n + (m + p)) ≡ suc (m + (n + p))
+-swap-suc zero n p = refl
+-swap-suc (suc m) n p rewrite +-suc n (m + p) | +-swap-suc n m p = refl


*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap-suc n m (m * n)= refl

-- 747/PLFA exercise: AddDistMult (2 points)
-- Show that addition distributes over multiplication.

*-+-rdistrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-+-rdistrib zero n p = refl
*-+-rdistrib (suc m) n p rewrite *-+-rdistrib m n p | +-assoc p (m * p) (n * p) = refl

-- 747/PLFA exercise: MultAssoc (2 points)
-- Show that multiplication is associative.

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-+-rdistrib n (m * n) p | *-assoc m n p = refl

-- 747/PLFA exercise: MultComm (3 points)
-- Show that multiplication is commutative.
-- As with the addition proof above, helper lemmas will be needed.

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-identityʳ n = refl
*-comm (suc m) n rewrite *-suc n m | *-comm n m = refl

-- 747/PLFA exercise: LeftMonusZero (1 point)
-- PLFA asks "Did your proof require induction?"
-- (which should give you an indication of the expected answer).

0∸n≡0 : ∀ (m : ℕ) → zero ∸ m ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc m) = refl

-- 747/PLFA exercise: MonusAssocish (2 points)
-- Show a form of associativity for monus.

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite 0∸n≡0 (n + p) | 0∸n≡0 n | 0∸n≡0 p = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

-- PLFA exercise (stretch): distributive and associative laws for exponentiation.

-- 747 extended exercise: properties of binary representation.
-- This is based on the PLFA Bin-laws exercise.

-- Copied from 747Naturals.

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

dbl-+ : ∀ (m n : ℕ) → dbl (m + n) ≡ dbl m + dbl n
dbl-+ zero n = refl
dbl-+ (suc m) zero rewrite +-identityʳ m | +-identityʳ (dbl m) = refl
dbl-+ (suc m) (suc n) rewrite dbl-+ m (suc n) = refl

-- Copy your versions of 'inc', 'to', 'from', 'bin-+' over from 747Naturals.
-- You may choose to change them here to make proofs easier.
-- But make sure to test them if you do!

inc : Bin-ℕ → Bin-ℕ
inc bits = bits x1
inc (m x0) = m x1
inc (m x1) = (inc m) x0

tob : ℕ → Bin-ℕ
tob zero = bits
tob (suc n) = inc (tob n)

fromb : Bin-ℕ → ℕ
fromb bits = 0
fromb (n x0) = 2 * fromb n
fromb (n x1) = suc ( 2 * fromb n )

_bin-+_ : Bin-ℕ → Bin-ℕ → Bin-ℕ
n bin-+ bits = n
bits bin-+ m = m
(n x0) bin-+ (m x0) = ( n bin-+ m ) x0
(n x1) bin-+ (m x0) = ( n bin-+ m ) x1
(n x0) bin-+ (m x1) = ( n bin-+ m ) x1
(n x1) bin-+ (m x1) = ( inc ( n bin-+ m ) ) x0

bin-+-identityᴸ : ∀ (m : Bin-ℕ) → bits bin-+ m ≡ m
bin-+-identityᴸ bits = refl
bin-+-identityᴸ (m x0) = refl
bin-+-identityᴸ (m x1) = refl

bin-+-identityʳ : ∀ (m : Bin-ℕ) → m bin-+ bits ≡ m
bin-+-identityʳ m = refl

-- 747 exercise: DoubleB (1 point)
-- Write the Bin-ℕ version of dbl, here called dblb.
-- As with the other Bin-ℕ operations, don't use tob/fromb.

dblb : Bin-ℕ → Bin-ℕ
dblb bits = bits
dblb (m x0) = (dblb m) x0
dblb (m x1) = (inc (dblb m)) x0

-- Here are some properties of tob/fromb/inc suggested by PLFA Induction.
-- Please complete the proofs.

-- 747 exercise: FromInc (1 point)

from∘inc : ∀ (m : Bin-ℕ) → fromb (inc m) ≡ suc (fromb m)
from∘inc bits = refl
from∘inc (m x0) = refl
from∘inc (m x1) rewrite +-identityʳ (fromb (inc m))
  | +-identityʳ (fromb m)
  | from∘inc m
  | +-suc (fromb m) (fromb m) = refl

-- 747 exercise: FromToB (1 point)

from∘tob : ∀ (m : ℕ) → fromb (tob m) ≡ m
from∘tob zero = refl
from∘tob (suc m) rewrite from∘inc (tob m) | from∘tob m = refl

-- 747 exercise: ToFromB (2 points)
-- The property ∀ (m : Bin-ℕ) → tob (fromb m) ≡ m cannot be proved.
-- Can you see why?
-- However, this restriction of it can be proved.

to/from-corr : ∀ (m : Bin-ℕ) (n : ℕ) → m ≡ tob n → fromb m ≡ n
to/from-corr m n m≡tn rewrite m≡tn | from∘tob n = refl

-- Here are a few more properties for you to prove.

-- 747 exercise: DblBInc (1 point)

dblb∘inc : ∀ (m : Bin-ℕ) → dblb (inc m) ≡ inc (inc (dblb m))
dblb∘inc bits = refl
dblb∘inc (m x0) = refl
dblb∘inc (m x1) rewrite dblb∘inc m = refl

-- 747 exercise: ToDbl (1 point)

to∘dbl : ∀ (m : ℕ) → tob (dbl m) ≡ dblb (tob m)
to∘dbl zero = refl
to∘dbl (suc m) rewrite dblb∘inc (tob m) | to∘dbl m = refl

-- 747 exercise: FromDblB (1 point)

from∘dblb : ∀ (m : Bin-ℕ) → fromb (dblb m) ≡ dbl (fromb m)
from∘dblb bits = refl
from∘dblb (m x0) rewrite +-identityʳ (fromb (dblb m))
  | +-identityʳ (fromb m)
  | from∘dblb m
  | dbl-+ (fromb m) (fromb m) = refl
from∘dblb (m x1) rewrite +-identityʳ (fromb (inc (dblb m)))
  | +-identityʳ (fromb m)
  | from∘inc (dblb m)
  | from∘dblb m
  | +-suc (dbl (fromb m)) (dbl (fromb m))
  | dbl-+ (fromb m) (fromb m) = refl

-- 747 exercise: BinPlusLInc (2 points)
-- This helper function translates the second case for unary addition
--  suc m + n = suc (m + n)
-- into the binary setting. It's useful in the next proof.
-- Hint: induction on both m and n is needed.

bin-+-linc : ∀ (m n : Bin-ℕ) → (inc m) bin-+ n ≡ inc (m bin-+ n)
bin-+-linc bits bits = refl
bin-+-linc bits (n x0) rewrite bin-+-identityᴸ n = refl
bin-+-linc bits (n x1) rewrite bin-+-identityᴸ n = refl
bin-+-linc (m x0) bits = refl
bin-+-linc (m x0) (n x0) = refl
bin-+-linc (m x0) (n x1) = refl
bin-+-linc (m x1) bits = refl
bin-+-linc (m x1) (n x0) rewrite bin-+-linc m n = refl
bin-+-linc (m x1) (n x1) rewrite bin-+-linc m n = refl

tob-+ : ∀ (m n : ℕ) → tob (m + n) ≡ tob m bin-+ tob n
tob-+ zero n rewrite bin-+-identityᴸ (tob n) = refl
tob-+ (suc m) n rewrite bin-+-linc (tob m) (tob n) | tob-+ m n = refl

-- 747 exercise: PlusUnaryBinary (2 points)
-- This theorem relates unary and binary addition.

to∘+ : ∀ (m n : ℕ) → tob (m + n) ≡ tob m bin-+ tob n
to∘+ zero n rewrite bin-+-identityᴸ (tob n) = refl
to∘+ (suc m) n rewrite bin-+-linc (tob m) (tob n) | tob-+ m n = refl

-- This ends the extended exercise.


-- The following theorems proved in PLFA can be found in the standard library.

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

-- Unicode used in this chapter:

{-

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

-}
