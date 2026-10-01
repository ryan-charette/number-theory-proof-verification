# Number Theory Library

This project formalizes elementary number theory in Lean, following *Number Theory Through Inquiry* by David C. Marshall, Edward Odell, and Michael Starbird (2007). The explanations are written for an introductory course in proofs.

## Overview

Each textbook subsection will have one self-contained Lean file. The current file, `01_divisibility.lean`, develops integer divisibility, congruence, powers, and decimal digit-sum tests. It ends before the division algorithm.

Each proof includes a statement in words, a step-by-step mathematical argument, and the corresponding Lean proof. All definitions and supporting results needed for this subsection appear in the same file. Only Lean's bundled integer arithmetic is imported; no other project files or external packages are required.

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
```

The file can also be copied into another Lean 4.12.0 project without copying any other source files from this repository. Import it with `import «01_divisibility»`. Its definitions and theorems are in the `NumberTheory` namespace.
