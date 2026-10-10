# Number Theory Library

This project formalizes elementary number theory in Lean, following *Number Theory Through Inquiry* by David C. Marshall, Edward Odell, and Michael Starbird (2007). The explanations are written for an introductory course in proofs.

## Overview

Each textbook subsection will have one self-contained Lean file. `01_divisibility.lean` develops integer divisibility, congruence, powers, and decimal digit-sum tests. `02_remainders.lean` proves quotient-and-remainder existence by well-ordering, uniqueness, and the equivalence between congruence and equal remainders. `03_common_divisors.lean` develops the Euclidean procedure and greatest common divisors, Bezout identities, coprimality, all solutions of integer linear equations, gcd scaling, and least common multiples. `04_factorization.lean` develops prime divisors, the trial-division bound, the sieve criterion, and existence and uniqueness of prime factorization. `05_divisibility_tests.lean` completes the next subsection: prime-exponent divisibility tests, divisibility of squares, impossible power equations, irrationality through integer-fraction equations, coprime gcd identities, and a divisibility pair among any n+1 positive inputs bounded by 2n. `06_prime_bounds.lean` develops coprimality of consecutive numbers, constructions avoiding small divisors, primes beyond every bound, preservation of remainder one modulo four under products, and infinitely many primes with remainder three modulo four. `07_power_factors.lean` proves geometric and odd-power factorization identities, then proves that primality of `2^n - 1` forces n to be prime and primality of `2^n + 1` for positive n forces n to be a power of two. `08_composite_runs.lean` constructs arbitrarily long runs of consecutive composite numbers using a product of initial integers and explicit factors for each entry. `09_polynomial_residues.lean` develops polynomial congruence, power-divisibility proofs, digit-sum tests, eventual polynomial growth, infinitely many composite absolute values, and existence, uniqueness, and counting of residue representatives. `10_modular_solutions.lean` develops the integer-equation and gcd criteria for solvability of a linear congruence, describes all its solution classes, and counts its canonical solutions.

Results presented only for context, which the reader is not expected to prove, are omitted.

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
lean 04_factorization.lean
lean 05_divisibility_tests.lean
lean 06_prime_bounds.lean
lean 07_power_factors.lean
lean 08_composite_runs.lean
lean 09_polynomial_residues.lean
lean 10_modular_solutions.lean
```

Each file can also be copied into another Lean 4.12.0 project without copying any other source files from this repository. Import a file with its quoted filename, such as `import «03_common_divisors»`. The namespaces are `NumberTheory`, `NumberTheory.Remainders`, `NumberTheory.CommonDivisors`, `NumberTheory.Factorization`, `NumberTheory.DivisibilityTests`, `NumberTheory.PrimeBounds`, `NumberTheory.PowerFactors`, `NumberTheory.CompositeRuns`, `NumberTheory.PolynomialResidues`, and `NumberTheory.ModularSolutions`, respectively. In the common-divisor file, positive integer hypotheses express the textbook convention that natural-number factors and lcm inputs are positive; solution formulas use exact integer quotients by the gcd.

Prime factorizations are represented as finite lists of primes. Repeated entries represent powers, as verified by `product_replicate`; occurrence counts record exponents. Uniqueness proves that any two factorizations are permutations and have the same primes and multiplicities. The trial-division bound uses `p * p ≤ n`, the integer equivalent of `p ≤ sqrt(n)`. The file proves its own primality and factorization results using elementary induction, Euclidean back-substitution, and cancellation.

The divisibility-tests file uses positive natural-number hypotheses to match the textbook convention. Prime exponents are occurrence counts in a chosen factor list; uniqueness makes these counts independent of the choice. Its irrationality statements rule out the equivalent equations `c * b ^ k = a ^ k` for integers `a`, `b` with `b ≠ 0`, including both signs, without requiring a real-number library. The general exponent obstruction also gives a family of further irrationality results. The finite counting proof explicitly removes factors of two, counts the possible odd parts, and retains distinct input positions even when values repeat. Gcd product identities include zero inputs; dividing both inputs by their gcd requires that they are not both zero.

The prime-bounds file expresses coprimality directly: every common natural divisor is one. It expresses infinitude by proving that every finite list omits a prime, and also omits a prime with remainder three modulo four. Both follow from explicit constructions of primes beyond any specified bound. A recursively defined product of initial integers supplies the construction; no library primality, factorization, or infinitude theorem is used.

The power-factors file uses explicit finite-sum and odd-power quotient witnesses. Integer arithmetic permits subtraction in these identities, and their natural-number consequences use the equivalence of integer and natural divisibility for nonnegative inputs. In the result for `2^n + 1`, n must be positive: zero would give the prime two but is not a power of two. The exponent in `n = 2^k` may be zero.

The composite-runs file describes a run by its positive starting number and its length. For any requested bound n, it constructs a run of length n+1 and proves every entry is a product of two smaller natural numbers. The construction includes n=0 and uses no library factorial or prime-distribution theorem.

The polynomial-residues file represents integer polynomials by coefficient lists in increasing power order. A nonconstant polynomial has at least two coefficients and a nonzero final coefficient. Growth is stated for arbitrary integer bounds; these are cofinal among real bounds. For the composite-value theorem, the approved sign correction uses the absolute value of the polynomial: the unrestricted original statement cannot hold with positive composite values for a polynomial such as `-x^2 - 1`. Infinitely many qualifying inputs are expressed by finding one above every integer bound. Residue systems are finite lists of distinct integers, and completeness means coverage with uniqueness modulo a positive modulus; their size is proved by elementary finite counting.

The modular-solutions file allows arbitrary integer coefficients and a positive modulus n. It reconstructs the gcd and Bezout coefficients by Euclidean induction so that the file stands alone. Given one solution, all integer solutions differ from it by a multiple of n/gcd(a,n). Reducing the parameter gives the finite family of solution classes. The exact count is expressed by a list with no repeated entries, of length gcd(a,n), whose members are precisely the solutions between zero and n-1. This includes zero coefficients and modulus one.
