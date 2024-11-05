# Number Theory Library

This project is a foundational Number Theory library developed using the Lean theorem prover. The library provides a set of modules, lemmas, and proofs grounded in the Peano axioms for the manipulation and analysis of natural numbers, focusing on properties such as addition, multiplication, and equality. Many of the theorems are taken from Michael Starbird's *Number Theory Through Inquiry* and the Natural Number game, available here: https://github.com/leanprover-community/lean4game

## Overview

The core library builds up basic properties of natural numbers starting from fundamental definitions, demonstrating how various arithmetic principles can be derived from first principles. While Lean's built-in arithmetic capabilities can often resolve low-level equalities automatically, this library illustrates these results using explicit proofs for pedagogical purposes.

## Key Components

- **Peano Axioms**: The library utilizes Peano’s axioms to derive properties of natural numbers systematically.
- **Arithmetic Proofs**: Includes proof of basic arithmetic properties such as:
  - Equality (reflexive and commutative)
  - Addition (associativity, commutativity, and distributivity)
  - Multiplication (associativity, commutativity, and properties with 1 and 0)
- **Rewrite Techniques**: The library leverages Lean’s `rw` (rewrite) tactic and related commands to manipulate expressions based on established lemmas.

## Main Features

### Example Theorems

- **Equality Proofs**: Proofs that validate basic equality properties, e.g., `2 + 2 = 4`, leveraging reflexivity (`rfl`).
- **Addition Properties**:
  - Commutativity of Addition: \( a + b = b + a \)
  - Associativity of Addition: \( (a + b) + c = a + (b + c) \)
  - Identity Elements: \( a + 0 = a \)
- **Multiplication Properties**:
  - Commutativity of Multiplication: \( a * b = b * a \)
  - Identity Elements: \( a * 1 = a \) and \( 0 * a = 0 \)
  - Distributive Properties for numbers such as \( 2 * m = m + m \)

### Tactics and Commands Used

- **Reflexivity (`rfl`)**: Used for proving simple goals of the form \( X = X \).
- **Rewrite (`rw`)**: Substitutes expressions based on previously proven equalities.
- **Induction**: Many proofs (e.g., commutativity and associativity of addition) are derived using mathematical induction.
- **nth_rewrite**: Allows for selective rewriting, e.g., rewriting only certain occurrences of a term.

## Example Proof

The following is an illustrative examples of a proof in this library:

   ```lean
   theorem add_comm (a b : Nat) : a + b = b + a := by
    /-
    Theorem: Addition of natural numbers is commutative. That is, for all
    a, b ∈ ℕ, a + b = b + a.
    Proof: We perform induction on a.
  
    Base case:
  
      0 + b = b + 0
  
      0 + b = b    [Peano's first axiom of addition]
  
      b = b        [Apply the `zero_add` theorem]
  
    Inductive case: Assume that d + b = b + d for some d ∈ ℕ.
  
      S(d) + b = b + S(d)
  
      S(d) + b = S(b + d)    [Peano's second axiom of addition]
  
      S(d + b) = S(b + d)    [Apply the `succ_add` theorem]
  
      S(b + d) = S(b + d)    [The inductive hypothesis]
  
    QED
    -/
    induction a with
    | zero =>
      rw [Nat.add_zero, Nat.zero_add]
    | succ d ih =>
      /-
      rw [← Nat.succ_eq_add_one] is needed because Lean uses d + 1 rather than
      S(d) for the inductive case.
      -/
      rw [← Nat.succ_eq_add_one, Nat.add_succ, Nat.succ_add, ih]
```
## Usage

To integrate this library, include it as part of your Lean project dependencies. You can then import individual modules as needed, depending on the arithmetic operations you intend to utilize.
```
import «Number Theory».Basic
```
This library serves as a foundational toolkit for performing formal proofs in number theory and can be extended to more complex operations and properties.

