# Number Theory Library

This project formalizes elementary number theory in Lean, following *Number Theory Through Inquiry* by David C. Marshall, Edward Odell, and Michael Starbird (2007). The explanations are written for an introductory course in proofs.

## Overview

Each textbook subsection will have one self-contained Lean file. `01_divisibility.lean` develops integer divisibility, congruence, powers, and decimal digit-sum tests. `02_remainders.lean` proves quotient-and-remainder existence by well-ordering, uniqueness, and the equivalence between congruence and equal remainders. `03_common_divisors.lean` develops the Euclidean procedure and greatest common divisors, Bezout identities, coprimality, all solutions of integer linear equations, gcd scaling, and least common multiples.

Each proof includes a statement in words, a step-by-step mathematical argument, and the corresponding Lean proof. All definitions and supporting results needed for each subsection appear in that subsection's file. Only Lean's bundled arithmetic and tactics are imported; no other project files or external packages are required. The tactic `omega` checks linear arithmetic after explicit mathematical arguments. The common-divisor file constructs its own gcd by Euclidean induction and back-substitution, then proves that it is greatest. Its lcm expression is proved to be the least positive common multiple; no library gcd, lcm, or Bezout theorem is used.

## Main Features

- Divisibility proofs construct an integer that gives the required multiple.
- Congruence is defined by a positive modulus dividing a difference.
- Arithmetic properties follow by substitution and ordinary arithmetic laws.
- Powers and digit-sum tests use induction, with the base case and induction step explained.
- The file contains proofs rather than computational exercises or textbook cross-references.

Lean's natural numbers include zero. The power theorem therefore includes exponent zero. Decimal expansions are finite lists of digits from 0 to 9, stored with the units digit first. The digit-sum tests apply to a supplied decimal representation, including zero and leading zeroes.

## Usage

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

The project pins Lean 4.12.0. To check the file directly with that version:

```sh
lean 01_divisibility.lean
lean 02_remainders.lean
lean 03_common_divisors.lean
```

Each file can also be copied into another Lean 4.12.0 project without copying any other source files from this repository. Import a file with its quoted filename, such as `import «03_common_divisors»`. The namespaces are `NumberTheory`, `NumberTheory.Remainders`, and `NumberTheory.CommonDivisors`, respectively. In the common-divisor file, positive integer hypotheses express the textbook convention that natural-number factors and lcm inputs are positive; solution formulas use exact integer quotients by the gcd.

## Completed daily work

- 2026-10-01 (America/Phoenix): `02_remainders.lean` — least-member principle, quotient-and-remainder existence and uniqueness, and congruence characterized by equal remainders.

- 2026-10-02 (America/Phoenix): `03_common_divisors.lean` — Euclidean construction, gcd and Bezout identities, coprimality, complete integer linear solutions, scaling, and least common multiples.
