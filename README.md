# A Lean companion to *Number Theory Through Inquiry*

This project follows the 2007 textbook by David C. Marshall, Edward Odell, and Michael Starbird. Each file covers one subsection. Alongside each Lean proof is a mathematical argument written for a reader taking a first course in proofs. Later subsections import the elementary results they use from earlier ones.

## Reading the proofs

Start with divisibility and congruence, or choose a topic below. The files are listed in textbook order. Open a file to read the argument, or use Lean in an editor to inspect the hypotheses and goal at each step.

### Divisibility and factorization

- [Divisibility and congruence](NumberTheory/Divisibility/01_divisibility.lean)
- [Quotients and remainders](NumberTheory/Divisibility/02_remainders.lean)
- [Common divisors and Bézout identities](NumberTheory/Divisibility/03_common_divisors.lean)
- [Prime factorizations](NumberTheory/Divisibility/04_factorization.lean)
- [Divisibility tests and prime exponents](NumberTheory/Divisibility/05_divisibility_tests.lean)

### Prime and composite numbers

- [Primes beyond any bound](NumberTheory/Primes/06_prime_bounds.lean)
- [Factors of powers plus or minus one](NumberTheory/Primes/07_power_factors.lean)
- [Runs of composite numbers](NumberTheory/Primes/08_composite_runs.lean)

### Congruences and modular powers

- [Polynomial values and residues](NumberTheory/Congruences/09_polynomial_residues.lean)
- [Solving linear congruences](NumberTheory/Congruences/10_modular_solutions.lean)
- [Simultaneous congruences](NumberTheory/Congruences/11_simultaneous_congruences.lean)
- [Cancellation and multiplicative order](NumberTheory/Congruences/12_modular_powers.lean)
- [Power cycles and Fermat’s theorem](NumberTheory/Congruences/13_power_cycles.lean)
- [Binomial coefficients and Fermat’s theorem](NumberTheory/Congruences/14_binomial_powers.lean)
- [Reduced residues and Euler’s theorem](NumberTheory/Congruences/15_reduced_residues.lean)
- [The arithmetic behind RSA](NumberTheory/Congruences/16_power_recovery.lean)

### Roots and residues

- [Roots of polynomials modulo a prime](NumberTheory/Residues/17_polynomial_roots.lean)
- [Counting elements by order](NumberTheory/Residues/18_order_counts.lean)
- [Totient sums and the number of primitive roots](NumberTheory/Residues/19_divisor_counts.lean)
- [Products and Euler’s totient](NumberTheory/Residues/20_totient_products.lean)
- [Roots of power congruences](NumberTheory/Residues/21_modular_roots.lean)
- [Testing primitive roots](NumberTheory/Residues/22_primitive_tests.lean)
- [Quadratic residues](NumberTheory/Residues/23_square_classes.lean)
- [Signs of quadratic residues](NumberTheory/Residues/24_residue_signs.lean)
- [Squares and primitive roots for primes of the form 2q + 1](NumberTheory/Residues/25_double_primes.lean)

### Integer right triangles

- [Primitive right triangles](NumberTheory/Triangles/26_right_triangles.lean) · 2026-10-25
- [Representations by two squares](NumberTheory/Triangles/27_square_pairs.lean) · 2026-10-27
- [Possible hypotenuses](NumberTheory/Triangles/28_hypotenuses.lean) · 2026-10-28
- [Fourth powers and infinite descent](NumberTheory/Triangles/29_fourth_powers.lean) · 2026-10-29

### Rational approximation and Pell equations

- [Approximating real numbers by fractions](NumberTheory/Approximation/30_approximations.lean) · 2026-10-30
- [Square parameters in Pell equations](NumberTheory/Approximation/31_square_parameters.lean) · 2026-10-31
- [Multiplying Pell solutions](NumberTheory/Approximation/32_pell_products.lean) · 2026-11-01
- [Existence of Pell solutions](NumberTheory/Approximation/33_pell_existence.lean) · 2026-11-02
- [Generating solutions by powers](NumberTheory/Approximation/34_pell_powers.lean) · 2026-11-03

### Testing for primality

- [Counting operations in primality tests](NumberTheory/Primality/35_test_costs.lean) · 2026-11-04
- [Power tests for compositeness](NumberTheory/Primality/36_power_tests.lean) · 2026-11-05
- [The binomial coefficient test](NumberTheory/Primality/37_coefficient_test.lean) · 2026-11-09

## Formalization choices

Congruence uses a positive modulus. The gcd is constructed by Euclidean division and back-substitution. A prime factorization is a list, so the exponent of a prime is its number of occurrences. The final binomial test compares coefficients of formal polynomials.

## Adding a subsection

Keep one numbered file per subsection and import earlier results where needed. Add the new module to [NumberTheory.lean](NumberTheory.lean) and link its source above. Make one commit per genuinely new theorem or supporting lemma. Explain any boundary corrections alongside the proof. Use Mathlib for foundational definitions and routine arithmetic, and give the elementary argument for each target theorem.

## Building the project

From the repository root, with Lean installed through elan, run:

```sh
lake exe cache get
lake build
```

The project pins Lean 4.12.0 and its Mathlib dependency. To check one subsection after building its imports, run:

```sh
lake env lean NumberTheory/Primality/37_coefficient_test.lean
```

Use `import NumberTheory` for the whole library, or import one module, for example `import NumberTheory.Divisibility.«02_remainders»`. The [library entry point](NumberTheory.lean) lists every subsection in reading order.
