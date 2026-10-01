# Number Theory Library

This project formalizes elementary number theory in Lean, following the results in David C. Marshall, Edward Odell, and Michael Starbird's *Number Theory Through Inquiry* (Mathematical Association of America, 2007). The current scope is items 1.1–1.24, on printed pages 9–14, stopping before the division algorithm. The explanations and proof comments are written for this project.

## Overview

The library develops divisibility and congruence over the integers. Proofs unpack definitions, construct integer witnesses, substitute equalities, and use ordinary arithmetic laws. Powers and decimal expansions are handled by induction. Each theorem keeps the worked-proof style: a statement, a proof in words with intermediate equalities, and the corresponding Lean steps.

## Key Components

| File | Contents | Textbook references |
| --- | --- | --- |
| `01_divisibility.lean` | Sums, differences, products, squares, and transitivity | 1.1–1.6 |
| `02_congruence.lean` | Definition, reflexivity, symmetry, transitivity, and arithmetic | 1.9–1.14 |
| `03_powers.lean` | Squares, cubes, the induction step, and arbitrary powers | 1.15–1.18 |
| `04_digits.lean` | Decimal expansions and digit-sum tests for 3 and 9 | 1.21–1.24, including the unnumbered equivalence after 1.21 |
| `05_examples.lean` | Numerical examples, congruence classes, and failed cancellation | 1.7–1.8, 1.19–1.20 |

Questions 1.4 and 1.5 are represented by proved strengthening and transitivity results. Exercise 1.24 is represented by the digit-sum test for 9. These are choices of answers to open-ended prompts.

## Main Features

- **Integer witnesses**: `a ∣ b` is used in its elementary form `∃ k : Int, b = a * k`.
- **Congruence from differences**: `a ≡ b [MOD n]` means `0 < n ∧ n ∣ a - b`. Positivity is part of the definition; this is project notation, not Lean's remainder-based congruence notation.
- **Natural exponents**: Lean's `Nat` includes zero. The power theorem includes exponent zero as a harmless strengthening of the positive-exponent result. The step from `k` to `k + 1` expresses the same step as the textbook's positive-exponent formulation.
- **Decimal digits**: A `List (Fin 10)` contains actual digits from 0 to 9, with the units digit first. For example, `[1, 3, 1, 1]` represents 1131. `decimalValue` and `digitSum` are recursive definitions. The tests take a supplied decimal representation; no digit-extraction algorithm is needed. Zero, empty expansions, and leading zeroes are also supported.
- **Elementary dependencies**: Only Lean's bundled integer arithmetic is imported. No Mathlib, abstract algebra, quotient structures, or pre-proved number-theory results are used to establish the general theorems.

### Tactics and Commands Used

- **`rcases` and `exists`**: Extract and construct divisibility witnesses.
- **`rw` and `simp only`**: Substitute equalities and apply explicitly listed arithmetic laws.
- **`constructor`, `intro`, and `exact`**: Assemble implications and the two directions of equivalences.
- **`induction`**: Prove the power and decimal-expansion results.
- **`rfl` and `decide`**: Check closed computations in examples and numerical facts such as positivity of 3. They do not replace the general proofs.

## Example Proof

```lean
theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b + c := by
  /-
  Theorem 1.1: A common divisor divides the sum.
  Proof: Write b = a * m and c = a * n. Then

    b + c = a * m + a * n    [Substitution]
          = a * (m + n)      [Distributivity]

  The integer m + n is the required witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m + n
  rw [hm, hn, Int.mul_add]
```

## Usage

Install Lean through [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake build
```

The `lean-toolchain` file pins Lean 4.12.0. There are no external package dependencies. The default build checks every numbered file, including the examples.

Import the complete library:

```lean
import NumberTheory

open NumberTheory

example (a b : Int) (h : a ≡ b [MOD 5]) : a ^ 4 ≡ b ^ 4 [MOD 5] := by
  exact modeq_pow a b 5 4 h
```

Or import a numbered module with a quoted Lean identifier, such as `import «02_congruence»`.
