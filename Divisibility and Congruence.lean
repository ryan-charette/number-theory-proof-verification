import «Number Theory».Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Init.Data.Int.DivModLemmas

theorem dvd_mult_left (a b : Int) : a ∣ (a * b) := by
  /-
  Theorem: a ∣ (a * b)
  Proof:

  ∃c : a * n = a * b    [Definition of divisible]

  a * b = a * b         [Let n := b]

  QED
  -/
  exists b

theorem dvd_mult_of_dvd_left (a b c : Int) (h : a ∣ b) : a ∣ (b * c) := by
  /-
  Theorem: If a ∣ b, then a ∣ (b * c)
  Proof:

  h₀ : a ∣ b             [True by hypothesis]
  h₁ : a ∣ c

  hn : ∃n : a * n = b    [Definition of divisible]

  a ∣ (b * c)

  a ∣ (a * n * c)        [Substitution via `hn`]

  a ∣ a * (n * c)        [Ring axioms]

  QED
  -/
  rcases h with ⟨n, hn⟩
  rw [hn]
  exists (n * c)
  ring

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ (b + c) := by
  /-
  Theorem: If a ∣ b and a ∣ c, then a ∣ (b + c)
  Proof:

  h₀ : a ∣ b             [True by hypothesis]
  h₁ : a ∣ c

  hm : ∃m : a * m = b    [Definition of divisible]
  hn : ∃n : a * n = c

  a ∣ (b + c)

  a ∣ (a * m + a * n)    [Substitution via `hm` and `hn`]

  a ∣ a * (m + n)        [Ring axioms]

  QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  rw [hm, hn]
  exists (m + n)
  ring

theorem dvd_sub (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ (b - c) := by
  /-
  Theorem: If a ∣ b and a ∣ c, then a ∣ (b - c)
  Proof:

  h₀ : a ∣ b             [True by hypothesis]
  h₁ : a ∣ c

  hm : ∃m : a * m = b    [Definition of divisible]
  hn : ∃n : a * n = c

  a ∣ (b - c)

  a ∣ (a * m - a * n)    [Substitution via `hm` and `hn`]

  a ∣ a * (m - n)        [Ring axioms]

  QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  rw [hm, hn]
  exists (m - n)
  ring

theorem dvd_mult_right (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ (b * c) :=
  by
  /-
  Theorem: If a ∣ b and a ∣ c, then a ∣ (b * c)
  Proof:

  h₀ : a ∣ b             [True by hypothesis]
  h₁ : a ∣ c

  hm : ∃m : a * m = b    [Definition of divisible]
  hn : ∃n : a * n = c

  a ∣ (b * c)

  a ∣ (a * m * a * n)    [Substitution via `hm` and `hn`]

  a ∣ a * (a * m * n)    [Ring axioms]

  QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  rw [hm, hn]
  exists (a * m * n)
  ring

theorem dvd_mult_right_sq (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) :
  a ^ 2 ∣ (b * c) := by
  /-
  Theorem: If a ∣ b and a ∣ c, then a ∣ (b * c)
  Proof:

  h₀ : a ∣ b             [True by hypothesis]
  h₁ : a ∣ c

  hm : ∃m : a * m = b    [Definition of divisible]
  hn : ∃n : a * n = c

  a ∣ (b * c)

  a ∣ (a * m * a * n)    [Substitution via `hm` and `hn`]

  a ∣ a ^ 2 * (m * n)    [Ring axioms]

  QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  rw [hm, hn]
  exists (m * n)
  ring

theorem modeq_refl (a n : Int) : a ≡ a [ZMOD n] := by
  /-
  Theorem: a ≡ a (mod n)
  Proof:

  a ≡ a (mod n)

  n ∣ a - a        [Definition of modular congruence]

  n ∣ 0            [Definition of additive inverse]

  ∃k: n * k = 0    [Definition of divisible]

  n * 0 = 0        [Let k := 0]

  0 = 0            [Zero product property]

  QED
  -/
  rw [Int.modEq_iff_dvd, Int.sub_self]
  exists (0)
  rw [Int.mul_zero]

theorem modeq_symm (a b n : Int) (h: a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  /-
  Theorem: If a ≡ b (mod n), then b ≡ a (mod n)
  Proof:

  a ≡ b (mod n)

  n ∣ a - b              [Definition of modular congruence]

  n * k = a - b          [Definition of divisible]

  -(n * k) = -(a - b)    [Multiply each side by negative 1]

  n * (-k) = (b - a)     [Ring axioms]

  n ∣ b - a              [Definition of divisible]

  b ≡ a (mod n)          [Definition of modular congruence]

  QED
  -/
  rw [Int.modEq_iff_dvd] at h
  rw [Int.modEq_iff_dvd]
  obtain ⟨k, hk⟩ := h
  use -k
  calc
    a - b = -(b - a) := by ring
    _ = n * -k       := by rw [hk, mul_neg]
