module 747Naturals where

-- This is a comment.

{-
  This is a multi-line comment
-}

-- Definition of datatype representing natural numbers.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- A couple of definitions using this datatype.

one : ℕ
one = suc zero

two : ℕ
two = suc (suc zero)

-- I could have also said two = suc one.

-- PLFA exercise: write out seven.

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- Pragma to use decimal notation as shorthand.

{-# BUILTIN NATURAL ℕ #-}

-- Some useful imports from the standard library:

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- Addition on naturals.

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)


-- Agda normalization; proof of equality.

_ : 2 + 3 ≡ 5
_ = refl

-- Equational reasoning.

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- many steps condensed
    5
  ∎

-- PLFA shows longhand and shorthand are interchangeable.

-- PLFA exercise: write out the reduction for 3+4 equationally.

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc ( suc (suc zero))) + (suc (suc (suc ( suc zero))))
  ≡⟨⟩
    7
  ∎

-- Multiplication.

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- many steps condensed
    6
  ∎

-- PLFA exercise: write out 3*4.

-- 747 exercise: Exponentiation (1 point)
-- Define exponentiation (m raised to the power n).

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * n ^ m


-- One test for exponentiation (you should write others).

_ : 2 ^ 3 ≡ 8
_ = refl

_ : 5 ^ 3 ≡ 125
_ = refl

_ : 0 ^ 0 ≡ 1
_ = refl

-- Monus (subtraction for naturals, bottoms out at zero).

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
     3 ∸ 2
  ≡⟨⟩ -- many steps condensed
     1
  ∎

_ =
  begin
     2 ∸ 3
  ≡⟨⟩ -- many steps condensed
     0
  ∎

-- PLFA exercise: write out 5 ∸ 3 and 3 ∸ 5.

infixl 6  _+_  _∸_
infixl 7  _*_

-- These pragmas will register our operations, if we want,
-- so that they work with decimal notation.

-- {-# BUILTIN NATPLUS _+_ #-}
-- {-# BUILTIN NATTIMES _*_ #-}
-- {-# BUILTIN NATMINUS _∸_ #-}

-- Binary representation.
-- Modified from PLFA exercise (thanks to David Darais).

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

-- Our representation of zero is different from PLFA.
-- We use the empty sequence of bits (more consistent).

bin-zero : Bin-ℕ
bin-zero = bits

bin-one : Bin-ℕ
bin-one = bits x1     -- 1 in binary

bin-two : Bin-ℕ
bin-two = bits x1 x0  -- 10 in binary

-- 747 exercise: Increment (1 point)
-- Define increment (add one).

inc : Bin-ℕ → Bin-ℕ
inc bits = bits x1
inc (m x0) = m x1
inc (m x1) = (inc m) x0

-- An example/test of increment (you should create others).

_ : inc (bits x1 x0 x1 x1) ≡ bits x1 x1 x0 x0
_ = refl

-- 747 exercise: To/From (2 points)
-- Define 'tob' and 'fromb' operations
-- to convert between unary (ℕ) and binary (Bin-ℕ) notation.
-- Hint: avoid addition and multiplication,
-- and instead use the provided dbl (double) function.
-- This will make later proofs easier.
-- I've put 'b' on the end of the operations to
-- avoid a name clash in a later file.
-- It also makes the direction clear when using them.

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc m) = suc (suc (dbl m))

tob : ℕ → Bin-ℕ
tob zero = bits
tob (suc n) = inc (tob n)

-- really want to say tob 2n = tob (N) x0 and tob (2n + 1) = tob (n) x1 but that's not working

fromb : Bin-ℕ → ℕ
fromb bits = 0
fromb (n x0) = 2 * fromb n
fromb (n x1) = suc ( 2 * fromb n )

-- A couple of examples/tests (you should create others).

_ : tob 6 ≡ bits x1 x1 x0
_ = refl

_ : tob 13 ≡ bits x1 x1 x0 x1
_ = refl

_ : fromb (bits x1 x1 x0) ≡ 6
_ = refl

_ : fromb (bits x1 x1 x0 x1) ≡ 13
_ = refl

-- 747 exercise: BinAdd (2 points)
-- Write the addition function for binary notation.
-- Do NOT use 'to' and 'from'. Work with Bin-ℕ as if ℕ did not exist.
-- Hint: use recursion on both m and n.

_bin-+_ : Bin-ℕ → Bin-ℕ → Bin-ℕ
n bin-+ bits = n
bits bin-+ (m x0) = m x0
(n x0) bin-+ (m x0) = ( n bin-+ m ) x0
(n x1) bin-+ (m x0) = ( n bin-+ m ) x1
bits bin-+ (m x1) = m x1
(n x0) bin-+ (m x1) = ( n bin-+ m ) x1
(n x1) bin-+ (m x1) = ( inc ( n bin-+ m ) ) x0

-- Tests can use to/from, or write out binary constants as below.
-- Again: write more tests!

_ : (bits x1 x0) bin-+ (bits x1 x1) ≡ (bits x1 x0 x1)
_ = refl

_ : (bits x1 x1 x1) bin-+ (bits x1 x0 x0) ≡ (bits x1 x0 x1 x1)
_ = refl

-- That's it for now, but we will return to binary notation later.

-- Many definitions from above are also in the standard library.

-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

-- Unicode used in this chapter:

{-
    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
-}
