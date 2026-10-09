import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PolynomialResidues

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b + c := by
  /-
  Theorem: A common divisor divides the sum.
  Proof: Write b = a * m and c = a * n. Then

    b + c = a * m + a * n    [Substitution]
          = a * (m + n)      [Distributivity]

  The integer m + n is the required witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m + n
  rw [hm, hn, Int.mul_add]

theorem dvd_mult_of_dvd_left (a b c : Int) (h : a ∣ b) : a ∣ b * c := by
  /-
  Theorem: If a divides b, then a divides b * c for any integer c.
  Proof: If b = a * m, then

    b * c = (a * m) * c = a * (m * c).

  Use m * c as the witness. QED
  -/
  rcases h with ⟨m, hm⟩
  exists m * c
  rw [hm, Int.mul_assoc]

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

local notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

theorem modeq_refl (a n : Int) (hn : 0 < n) : a ≡ a [MOD n] := by
  /-
  Theorem: Every integer is congruent to itself.
  Proof: The modulus n is positive by hypothesis. Also,

    a - a = 0 = n * 0.

  Thus n divides a - a, using the integer 0. QED
  -/
  constructor
  · exact hn
  · exists 0
    rw [Int.sub_self, Int.mul_zero]

theorem modeq_symm (a b n : Int) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  /-
  Theorem: Reversing a congruence preserves it.
  Proof: By the definition of congruence, n is positive and
  a - b = n * k for some integer k. Then

    b - a = -(a - b) = -(n * k) = n * (-k).

  Use -k as the witness. QED
  -/
  rcases h with ⟨hn, k, hk⟩
  constructor
  · exact hn
  · exists -k
    rw [← Int.neg_sub a b, hk, Int.mul_neg]

theorem modeq_trans (a b c n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  /-
  Theorem: Two consecutive congruences combine.
  Proof: The hypotheses tell us that n divides a - b and b - c.
  Therefore n divides their sum. Adding the differences gives:

    (a - b) + (b - c) = a - c.

  Both differences are divisible by n, so their sum is too. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (b - c) h₀.2 h₁.2
    rw [← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem modeq_add (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  /-
  Theorem: Congruences can be added.
  Proof: We must show that n divides (a + c) - (b + d).
  Rearranging the additions and subtractions gives

    (a + c) - (b + d) = (a - b) + (c - d).

  By hypothesis, n divides each term on the right. Our theorem on
  divisibility of sums shows that n divides the left side as well. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (c - d) h₀.2 h₁.2
    have heq : (a + c) - (b + d) = (a - b) + (c - d) := by
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]
      rw [Int.add_left_comm c (-b)]
    rw [heq]
    exact h

theorem modeq_mult (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] := by
  /-
  Theorem: Congruences can be multiplied.
  Proof: We must show that n divides a * c - b * d. We can express
  this difference in terms of a - b and c - d:

    a * c - b * d = a * c - b * c + b * c - b * d
                 = (a - b) * c + b * (c - d).

  Since n divides a - b, it divides (a - b) * c. Similarly, since n
  divides c - d, it divides b * (c - d). It therefore divides their
  sum, which is a * c - b * d. QED
  -/
  constructor
  · exact h₀.1
  · have h₂ := dvd_mult_of_dvd_left n (a - b) c h₀.2
    have h₃ := dvd_mult_of_dvd_left n (c - d) b h₁.2
    have h := dvd_add n ((a - b) * c) ((c - d) * b) h₂ h₃
    rw [Int.mul_comm (c - d) b, Int.sub_mul, Int.mul_sub,
      ← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem modeq_pow_step (a b n : Int) (k : Nat)
    (h : a ≡ b [MOD n]) (hk : a ^ k ≡ b ^ k [MOD n]) :
    a ^ (k + 1) ≡ b ^ (k + 1) [MOD n] := by
  /-
  Theorem: Advance an exponent by one.
  Proof: a ^ (k + 1) = a ^ k * a, and likewise for b.
  Multiply the two assumed congruences. QED
  -/
  rw [Int.pow_succ, Int.pow_succ]
  exact modeq_mult (a ^ k) (b ^ k) a b n hk h

theorem modeq_pow (a b n : Int) (k : Nat) (h : a ≡ b [MOD n]) :
    a ^ k ≡ b ^ k [MOD n] := by
  /-
  Theorem: Every natural-number power preserves congruence.
  Proof: We use induction on k, including zero.

  Base case: When k = 0, both powers are 1. We have already shown
  that every integer is congruent to itself.

  Inductive case: Suppose a ^ k is congruent to b ^ k modulo n.
  We also know that a is congruent to b modulo n. Multiplying these
  congruences gives

    a ^ k * a ≡ b ^ k * b [MOD n].

  These products are a ^ (k + 1) and b ^ (k + 1), as required.

  QED
  -/
  induction k with
  | zero =>
    rw [Int.pow_zero, Int.pow_zero]
    exact modeq_refl 1 n h.1
  | succ k ih =>
    exact modeq_pow_step a b n k h ih


def evaluate : List Int → Int → Int
  | [], _ => 0
  | a :: cs, x => a + x * evaluate cs x

theorem polynomial_congruence (cs : List Int) (a b m : Int)
    (h : a ≡ b [MOD m]) : evaluate cs a ≡ evaluate cs b [MOD m] := by
  /-
  Theorem: An integer polynomial takes congruent values at congruent
  integer inputs. Proof: Store coefficients in increasing power order.
  The empty list evaluates to zero. For a first coefficient c and
  remaining polynomial g, the polynomial is c+x*g(x). Induction
  gives g(a) congruent to g(b). Multiply this by the input congruence
  and add c to obtain the desired congruence. QED

  This list representation includes every integer polynomial. The
  proof also covers constant polynomials and leading zero coefficients.
  -/
  induction cs with
  | nil => exact modeq_refl 0 m h.1
  | cons c cs ih =>
    exact modeq_add c c (a*evaluate cs a) (b*evaluate cs b) m
      (modeq_refl c m h.1) (modeq_mult a b (evaluate cs a) (evaluate cs b) m h ih)


theorem congruent_dvd_iff (a b m : Int) (h : a ≡ b [MOD m]) : m ∣ a ↔ m ∣ b := by
  /-
  Lemma: Congruent integers are either both divisible by their modulus
  or neither is. Proof: Write a-b=m*t. If a=m*u, then b=m*(u-t).
  Conversely, if b=m*u, then a=m*(u+t). These are explicit witnesses.
  QED
  -/
  rcases h.2 with ⟨t,ht⟩
  constructor
  · rintro ⟨u,hu⟩
    exists u-t
    rw [Int.mul_sub]
    omega
  · rintro ⟨u,hu⟩
    exists u+t
    rw [Int.mul_add]
    omega


def digitCoefficients (digits : List (Fin 10)) : List Int := digits.map (fun d => (d.val : Int))
def decimalValue (digits : List (Fin 10)) : Int := evaluate (digitCoefficients digits) 10
def digitSum (digits : List (Fin 10)) : Int := evaluate (digitCoefficients digits) 1

theorem nine_dvd_iff_digit_sum (digits : List (Fin 10)) :
    (9 : Int) ∣ decimalValue digits ↔ (9 : Int) ∣ digitSum digits := by
  /-
  Corollary: A decimal number is divisible by nine exactly when the
  sum of its digits is. Proof: Regard its digits, units first, as
  polynomial coefficients. Evaluation at ten gives the number;
  evaluation at one gives the sum of its digits. Since 10-1=9,
  the inputs are congruent modulo nine. Polynomial congruence makes
  the two values congruent, so divisibility by nine is equivalent.
  Leading zero digits and the empty representation are allowed. QED
  -/
  exact congruent_dvd_iff _ _ 9
    (polynomial_congruence (digitCoefficients digits) 10 1 9 ⟨by decide,1,by decide⟩)


theorem three_dvd_iff_digit_sum (digits : List (Fin 10)) :
    (3 : Int) ∣ decimalValue digits ↔ (3 : Int) ∣ digitSum digits := by
  /-
  Corollary: A decimal number is divisible by three exactly when its
  digit sum is. Proof: The digit polynomial evaluated at ten gives
  the number and at one gives the sum. The difference 10-1=3*3
  makes these inputs congruent modulo three. Apply polynomial
  congruence and the divisibility equivalence. QED
  -/
  exact congruent_dvd_iff _ _ 3
    (polynomial_congruence (digitCoefficients digits) 10 1 3 ⟨by decide,3,by decide⟩)


def leading : List Int → Int
  | [] => 0
  | [a] => a
  | _ :: b :: cs => leading (b :: cs)

theorem positive_leading_lower_bound (cs : List Int) (hl : 0 < leading cs) :
    ∃ K : Int, ∀ x : Int, K < x → 1 ≤ evaluate cs x := by
  /-
  Lemma: An integer polynomial with positive leading coefficient is
  at least one for all sufficiently large integer inputs.
  Proof: Induct on its coefficient list. A positive constant is at
  least one. Otherwise write f(x)=c+x*g(x). The leading coefficient
  of g is still positive, so g(x)≥1 beyond some bound by induction.
  Choose x beyond that bound, zero, and 1-c. Then x*g(x)≥x and
  f(x)≥c+x≥1. The empty list has leading coefficient zero and is
  excluded. No limit or analytic growth result is used. QED
  -/
  induction cs with
  | nil => simp [leading] at hl
  | cons c cs ih =>
    cases cs with
    | nil =>
      refine ⟨0,?_⟩
      intro x _
      simp only [leading] at hl
      simp only [evaluate,Int.mul_zero,Int.add_zero]
      omega
    | cons d ds =>
      rcases ih hl with ⟨K,hK⟩
      refine ⟨max K (max 0 (1-c)),?_⟩
      intro x hx
      have htail := hK x (by omega)
      have hmul := Int.mul_le_mul_of_nonneg_left htail (by omega : 0 ≤ x)
      rw [Int.mul_one] at hmul
      change 1 ≤ c+x*evaluate (d::ds) x
      omega


theorem polynomial_eventually_positive (cs : List Int) (hl : 0 < leading cs) :
    ∃ K : Int, ∀ x : Int, K < x → 0 < evaluate cs x := by
  /-
  Theorem: A polynomial with positive leading coefficient is eventually
  positive. Proof: The preceding lower bound gives value at least one
  past an integer threshold, and hence strictly greater than zero.
  This also covers positive constant polynomials. QED
  -/
  rcases positive_leading_lower_bound cs hl with ⟨K,hK⟩
  exact ⟨K,fun x hx => by have := hK x hx; omega⟩


theorem polynomial_eventually_above (cs : List Int) (hdegree : 2 ≤ cs.length)
    (hl : 0 < leading cs) (M : Int) :
    ∃ K : Int, ∀ x : Int, K < x → M < evaluate cs x := by
  /-
  Theorem: A nonconstant integer polynomial with positive leading
  coefficient eventually exceeds any prescribed bound.
  Proof: Write f(x)=c+x*g(x), where g has positive leading coefficient.
  Beyond a threshold, g(x)≥1. Also require x>0 and x>M-c. Then
  f(x)≥c+x>M. Taking the largest of these thresholds proves the claim.
  For a real bound, choose an integer above it first; the integer-bound
  formulation therefore expresses the same unbounded-growth assertion.
  QED
  -/
  cases cs with
  | nil => simp at hdegree
  | cons c cs =>
    cases cs with
    | nil => simp at hdegree
    | cons d ds =>
      rcases positive_leading_lower_bound (d::ds) hl with ⟨K,hK⟩
      refine ⟨max K (max 0 (M-c)),?_⟩
      intro x hx
      have htail := hK x (by omega)
      have hmul := Int.mul_le_mul_of_nonneg_left htail (by omega : 0 ≤ x)
      rw [Int.mul_one] at hmul
      change M < c+x*evaluate (d::ds) x
      omega


theorem evaluate_negated (cs : List Int) (x : Int) :
    evaluate (cs.map (fun a => -a)) x = -evaluate cs x := by
  /-
  Lemma: Negating every coefficient negates the polynomial's value.
  Proof: Induct on the coefficient list. Zero negates to zero. At a
  further coefficient, -c+x*(-g(x))=-(c+x*g(x)) by distributivity
  and the induction hypothesis. QED
  -/
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons,evaluate,ih,Int.mul_neg,Int.neg_add]


theorem leading_negated (cs : List Int) :
    leading (cs.map (fun a => -a)) = -leading cs := by
  /-
  Lemma: Negating the coefficients negates the leading coefficient.
  Proof: The empty list has leading coefficient zero; a singleton's
  leading coefficient is its entry. For a longer list, discard the
  first coefficient and apply induction to the remaining list. QED
  -/
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds => exact ih


theorem polynomial_abs_eventually_above (cs : List Int) (hdegree : 2 ≤ cs.length)
    (hl : leading cs ≠ 0) (M : Int) :
    ∃ K : Int, ∀ x : Int, K < x → M < (evaluate cs x).natAbs := by
  /-
  Lemma: Absolute values of a nonconstant integer polynomial eventually
  exceed every bound. Proof: If the leading coefficient is positive,
  use positive growth and |f(x)|≥f(x). Otherwise negate all coefficients.
  The new leading coefficient is positive and its value is -f(x).
  Apply growth there and use |f(x)|≥-f(x). QED
  -/
  by_cases hp : 0 < leading cs
  · rcases polynomial_eventually_above cs hdegree hp M with ⟨K,hK⟩
    refine ⟨K,?_⟩
    intro x hx
    have h := hK x hx
    have hb : evaluate cs x ≤ (evaluate cs x).natAbs := Int.le_natAbs
    omega
  · have hneg : 0 < leading (cs.map (fun a => -a)) := by rw [leading_negated]; omega
    rcases polynomial_eventually_above (cs.map (fun a => -a))
      (by simpa using hdegree) hneg M with ⟨K,hK⟩
    refine ⟨K,?_⟩
    intro x hx
    have h := hK x hx
    rw [evaluate_negated] at h
    have hb : -evaluate cs x ≤ (-evaluate cs x).natAbs := Int.le_natAbs
    rw [Int.natAbs_neg] at hb
    omega


theorem progression_above (a d B : Int) (hd : 0 < d) :
    ∃ x : Int, B < x ∧ x ≡ a [MOD d] := by
  /-
  Lemma: A congruence class with positive modulus has members above
  any bound. Proof: Take t=|B-a|+1 and x=a+d*t. Since d≥1 and
  t>0, d*t≥t>B-a, so x>B. Also x-a=d*t, as required. QED
  -/
  let t : Int := (B-a).natAbs+1
  have hb : B-a ≤ (B-a).natAbs := Int.le_natAbs
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hmul := Int.mul_le_mul_of_nonneg_right (by omega : 1 ≤ d) ht
  rw [Int.one_mul] at hmul
  refine ⟨a+d*t,?_,hd,t,?_⟩
  · dsimp [t] at *
    omega
  · omega


def Composite (n : Nat) : Prop := ∃ a b : Nat, a < n ∧ b < n ∧ n=a*b

theorem composite_of_divisor (n d : Nat) (hd : 1 < d) (hdn : d < n) (h : d ∣ n) :
    Composite n := by
  /-
  Lemma: A number with a divisor strictly between one and itself is
  composite. Proof: Write n=d*q. The quotient q is positive and
  cannot be one, since d<n. As d>1, q<d*q=n. Thus d and q are
  both smaller factors of n, proving compositeness. QED
  -/
  rcases h with ⟨q,hq⟩
  have hpos : 0 < q := by
    by_cases hz : q=0
    · simp [hz] at hq
      omega
    · omega
  have hsmall := Nat.mul_lt_mul_of_pos_right hd hpos
  rw [Nat.one_mul,←hq] at hsmall
  exact ⟨d,q,hdn,hsmall,hq⟩


theorem composite_polynomial_values (cs : List Int) (hdegree : 2 ≤ cs.length)
    (hl : leading cs ≠ 0) (B : Int) :
    ∃ x : Int, B < x ∧ Composite (evaluate cs x).natAbs := by
  /-
  Theorem: For every nonconstant integer polynomial and every input
  bound B, some x>B has composite |f(x)|. Thus infinitely many integer
  inputs give composite absolute values.
  Proof: Growth of |f| gives an input a with d=|f(a)|>1. In the
  congruence class a modulo d, polynomial congruence ensures that d
  divides f(x), since it divides f(a). Choose x in this class beyond
  B and beyond a threshold where |f(x)|>d. Then d is a divisor
  strictly between one and |f(x)|, proving that |f(x)| is composite.
  QED

  Sign correction: The source statement allows negative leading
  coefficients but defines composite only for natural numbers. For
  example -x^2-1 is always negative. As approved, this theorem uses
  |f(x)|, without restricting the sign of the leading coefficient.
  -/
  rcases polynomial_abs_eventually_above cs hdegree hl 1 with ⟨K,hK⟩
  let a := K+1
  let d := (evaluate cs a).natAbs
  have hd : 1 < d := by have h := hK a (by dsimp [a]; omega); omega
  rcases polynomial_abs_eventually_above cs hdegree hl d with ⟨L,hL⟩
  rcases progression_above a d (max B L) (by omega) with ⟨x,hx,hcong⟩
  have hbig := hL x (by omega)
  have hf := polynomial_congruence cs x a d hcong
  have hdiv : (d : Int) ∣ evaluate cs x :=
    (congruent_dvd_iff _ _ _ hf).mpr Int.natAbs_dvd_self
  have hnat := Int.natAbs_dvd_natAbs.mpr hdiv
  rw [Int.natAbs_ofNat] at hnat
  exact ⟨x,by omega,composite_of_divisor _ d hd (by omega) hnat⟩


theorem forty_one_dvd_power_difference : (41 : Int) ∣ 2^20-1 := by
  /-
  Theorem: Forty-one divides 2^20-1.
  Proof: Since 2^5-(-9)=41, we have 2^5 congruent to -9. Taking
  fourth powers gives 2^20 congruent to (-9)^4. The latter differs
  from one by 6560=41*160. Transitivity gives the desired divisibility.
  The arithmetic checks concern only these small reduced values. QED
  -/
  have h : (2 : Int)^5 ≡ -9 [MOD 41] := ⟨by decide,1,by decide⟩
  have hp := modeq_pow _ _ _ 4 h
  have hlast : (-9 : Int)^4 ≡ 1 [MOD 41] := ⟨by decide,160,by decide⟩
  have he := modeq_trans _ _ _ _ hp hlast
  exact he.2


theorem thirty_nine_dvd_power_difference : (39 : Int) ∣ 17^48-5^24 := by
  /-
  Theorem: Thirty-nine divides 17^48-5^24.
  Proof: Since 17^2=289 is congruent to 16, and 16^3=4096 is
  congruent to one, 17^6 is congruent to one. Taking eighth powers
  gives 17^48 congruent to one. Also 5^3=125 is
  congruent to 8; 8^4=4096 is congruent to one. Therefore 5^12 is
  congruent to one, and squaring gives 5^24 congruent to one.
  Subtracting these congruences proves the asserted divisibility. QED
  -/
  have h17 : (17 : Int)^2 ≡ 16 [MOD 39] := ⟨by decide,7,by decide⟩
  have h16 : (16 : Int)^3 ≡ 1 [MOD 39] := ⟨by decide,105,by decide⟩
  have h17six := modeq_trans _ _ _ _ (modeq_pow _ _ _ 3 h17) h16
  have h17large := modeq_pow _ _ _ 8 h17six
  have h5 : (5 : Int)^3 ≡ 8 [MOD 39] := ⟨by decide,3,by decide⟩
  have h8 : (8 : Int)^4 ≡ 1 [MOD 39] := ⟨by decide,105,by decide⟩
  have h5twelve := modeq_trans _ _ _ _ (modeq_pow _ _ _ 4 h5) h8
  have h5large := modeq_pow _ _ _ 2 h5twelve
  have he := modeq_trans _ _ _ _ h17large (modeq_symm _ _ _ h5large)
  exact he.2

theorem least_natural (P : Nat → Prop) (h : ∃ b, P b) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b := by
  /-
  Theorem: A nonempty collection of natural numbers has a least member.
  Proof: We prove by strong induction on b that if b is a member, the
  collection has a least member. Strong induction allows us to assume
  the assertion for every natural number smaller than b.

  If some member a is smaller than b, the induction hypothesis at a
  gives a least member. If no member is smaller than b, then b itself
  is least. Finally, nonemptiness supplies a member to start with. QED
  -/
  letI := Classical.propDecidable
  have least_below : ∀ b, P b → ∃ a, P a ∧ ∀ c, P c → a ≤ c := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb
      by_cases hs : ∃ a, a < b ∧ P a
      · rcases hs with ⟨a, hab, ha⟩
        exact ih a hab ha
      · exists b
        constructor
        · exact hb
        · intro c hc
          apply Nat.le_of_not_lt
          intro hcb
          exact hs ⟨c, hcb, hc⟩
  rcases h with ⟨b, hb⟩
  exact least_below b hb

theorem division_exists (m n : Nat) (hn : 0 < n) :
    ∃ q r : Int, (m : Int) = (n : Int) * q + r ∧ 0 ≤ r ∧ r < (n : Int) := by
  /-
  Theorem: For a natural number m and a positive natural number n,
  there are integers q and r with m = n * q + r and 0 ≤ r < n.
  Lean includes zero among the natural numbers, so we explicitly require
  n > 0. The conclusion also holds when m = 0.

  Proof: Consider all nonnegative integers r for which m = n * q + r
  for some integer q. This collection is nonempty: q = 0 and r = m
  satisfy the equation. Choose its least member r by well-ordering,
  and choose an integer q giving the equation.

  If r ≥ n, then r - n is nonnegative and

    m = n * q + r = n * (q + 1) + (r - n).

  Thus r - n is another member of the collection. Since n > 0,
  it is smaller than r, contradicting the choice of r. Hence r < n.
  The chosen q and r have all the required properties. QED
  -/
  let P : Nat → Prop := fun r => ∃ q : Int, (m : Int) = (n : Int) * q + r
  have hnonempty : ∃ r, P r := by
    exists m
    exists (0 : Int)
    rw [Int.mul_zero, Int.zero_add]
  rcases least_natural P hnonempty with ⟨r, hr, hleast⟩
  rcases hr with ⟨q, hq⟩
  have hsmall : r < n := by
    apply Nat.lt_of_not_ge
    intro hlarge
    have hnext : P (r - n) := by
      exists q + 1
      rw [Int.mul_add, Int.mul_one]
      -- Since n ≤ r, natural subtraction agrees with integer subtraction.
      omega
    have hminimal := hleast (r - n) hnext
    -- Subtracting positive n gives a strictly smaller natural number.
    omega
  exists q, (r : Int)
  exact ⟨hq, by omega, by omega⟩

theorem division_unique (m n q r q' r' : Int) (hn : 0 < n)
    (h : m = n * q + r) (h' : m = n * q' + r')
    (hr : 0 ≤ r) (hrn : r < n) (hr' : 0 ≤ r') (hrn' : r' < n) :
    q = q' ∧ r = r' := by
  /-
  Theorem: Two decompositions with the same positive divisor and
  remainders between zero and n - 1 have equal quotients and remainders.
  We allow any integer m, which also covers natural-number dividends.

  Proof: Suppose m = n * q + r = n * q' + r'. If q < q', the
  quotients are integers, so q + 1 ≤ q'. Multiplying by positive n,

    n * q + n ≤ n * q'.

  But r < n and r' ≥ 0 give

    m = n * q + r < n * q + n ≤ n * q' ≤ n * q' + r' = m.

  This is impossible. Interchanging the two decompositions rules out
  q' < q in exactly the same way. Therefore q = q'. Substituting into
  the original equations and cancelling n * q gives r = r'. QED
  -/
  have hnot : ¬ q < q' := by
    intro hlt
    have hstep : q + 1 ≤ q' := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hstep (Int.le_of_lt hn)
    rw [Int.mul_add, Int.mul_one] at hmul
    -- The remainder bounds would force m < m.
    omega
  have hnot' : ¬ q' < q := by
    intro hlt
    have hstep : q' + 1 ≤ q := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hstep (Int.le_of_lt hn)
    rw [Int.mul_add, Int.mul_one] at hmul
    omega
  have hq : q = q' := by omega
  constructor
  · exact hq
  · rw [hq] at h
    omega


theorem integer_division_exists (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ q r : Int, a=(n : Int)*q+r ∧ 0 ≤ r ∧ r < n := by
  /-
  Lemma: Every integer has a quotient and a nonnegative remainder
  less than a positive natural divisor n.
  Proof: Let t=|a|. Since n≥1, a+n*t≥a+|a|≥0. Divide this
  nonnegative integer by n using the well-ordering construction.
  If a+n*t=n*q+r, then a=n*(q-t)+r, with the same remainder bounds.
  QED
  -/
  let t : Int := a.natAbs
  have ht : 0 ≤ t := by dsimp [t]; omega
  have ha : -a ≤ t := by
    have h : -a ≤ (-a).natAbs := Int.le_natAbs
    simpa only [Int.natAbs_neg] using h
  have hmul := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ n) ht
  rw [Int.one_mul] at hmul
  have hnonneg : 0 ≤ a+(n : Int)*t := by omega
  rcases division_exists (a+(n : Int)*t).toNat n hn with ⟨q,r,he,hr,hrn⟩
  rw [Int.toNat_of_nonneg hnonneg] at he
  refine ⟨q-t,r,?_,hr,hrn⟩
  rw [Int.mul_sub]
  omega


theorem bounded_congruent_equal (r s m : Int) (hr : 0 ≤ r) (hrm : r < m)
    (hs : 0 ≤ s) (hsm : s < m) (h : r ≡ s [MOD m]) : r=s := by
  /-
  Lemma: Two congruent integers between zero and m-1 are equal.
  Proof: Write r-s=m*q. Then r=m*q+s and also r=m*0+r.
  Both remainders satisfy the required bounds, so uniqueness of
  quotient and remainder makes r=s. QED
  -/
  rcases h.2 with ⟨q,hq⟩
  exact (division_unique r m 0 r q s h.1 (by simp) (by omega)
    hr hrm hs hsm).2


theorem canonical_residue (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ r : Int, 0 ≤ r ∧ r < n ∧ a ≡ r [MOD (n : Int)] ∧
      ∀ s : Int, 0 ≤ s → s < n → a ≡ s [MOD (n : Int)] → s=r := by
  /-
  Theorem: Every integer is congruent to exactly one integer among
  zero through n-1, for positive n.
  Proof: Division gives a=n*q+r with 0≤r<n, so a-r=n*q proves
  congruence. If s is another such representative, reverse the
  congruence a≡s and combine it with a≡r to get s≡r. Bounded
  congruent representatives are equal. QED
  -/
  rcases integer_division_exists a n hn with ⟨q,r,he,hr,hrn⟩
  have hcong : a ≡ r [MOD (n : Int)] := ⟨by omega,q,by omega⟩
  refine ⟨r,hr,hrn,hcong,?_⟩
  intro s hs hsn hsc
  exact bounded_congruent_equal s r n hs hsn hr hrn
    (modeq_trans s a r n (modeq_symm a s n hsc) hcong)


noncomputable def canonicalLabel (a : Int) (n : Nat) : Nat :=
  if h : 0 < n then (Classical.choose (canonical_residue a n h)).toNat else 0

theorem canonicalLabel_spec (a : Int) (n : Nat) (hn : 0 < n) :
    canonicalLabel a n < n ∧ a ≡ (canonicalLabel a n : Int) [MOD (n : Int)] := by
  /-
  Lemma: The canonical label is less than n and represents its input.
  Proof: Choose the unique representative already proved to exist.
  It is nonnegative, so conversion to a natural number preserves its
  value and both stated properties. At modulus zero the definition
  is total by convention, but the lemma requires positive modulus.
  QED
  -/
  have h := Classical.choose_spec (canonical_residue a n hn)
  have hcast := Int.toNat_of_nonneg h.1
  unfold canonicalLabel
  rw [dif_pos hn]
  constructor
  · omega
  · rw [Int.toNat_of_nonneg h.1]
    exact h.2.2.1



theorem canonicalLabel_eq_iff (a b : Int) (n : Nat) (hn : 0 < n) :
    canonicalLabel a n = canonicalLabel b n ↔ a ≡ b [MOD (n : Int)] := by
  /-
  Lemma: Two inputs have the same canonical label exactly when they
  are congruent. Proof: Equal labels give a common representative;
  transitivity yields congruence of the inputs. Conversely, congruent
  inputs have congruent labels by symmetry and transitivity. Both
  labels lie between zero and n-1, so they are equal. QED
  -/
  have ha := canonicalLabel_spec a n hn
  have hb := canonicalLabel_spec b n hn
  constructor
  · intro he
    have hac := ha.2
    rw [he] at hac
    exact modeq_trans a (canonicalLabel b n) b n hac (modeq_symm b _ n hb.2)
  · intro h
    have hlabels := modeq_trans (canonicalLabel a n) a (canonicalLabel b n) n
      (modeq_symm a _ n ha.2) (modeq_trans a b _ n h hb.2)
    have he := bounded_congruent_equal (canonicalLabel a n) (canonicalLabel b n) n
      (by omega) (by omega) (by omega) (by omega) hlabels
    omega

theorem distinct_length_bound (xs ys : List Nat) (h : xs.Nodup)
    (hsub : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  /-
  Lemma: A list of distinct entries drawn from a list of available
  values cannot be longer than that list.
  Proof: Induct on the list of distinct entries. The empty case is
  immediate. Remove the first entry from both lists. No entry in the
  first tail equals the removed entry, so all its entries remain
  available. Induction bounds the tail length. Restoring the removed
  entry adds one to each length and proves the required bound. QED
  -/
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have hh := List.nodup_cons.mp h
    have ha := hsub a (by simp)
    have ht : ∀ b ∈ xs, b ∈ ys.erase a := by
      intro b hb
      have hne : b ≠ a := by intro he; subst b; exact hh.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hsub b (by simp [hb]))
    have hb := ih (ys.erase a) hh.2 ht
    have hl := List.length_erase_of_mem ha
    have hn : 0 < ys.length := by
      cases ys with
      | nil => cases ha
      | cons b bs => simp
    simp only [List.length_cons]
    omega


def Noncongruent (reps : List Int) (n : Nat) : Prop :=
  reps.Nodup ∧ ∀ a ∈ reps, ∀ b ∈ reps, a ≡ b [MOD (n : Int)] → a=b

def CompleteResidues (reps : List Int) (n : Nat) : Prop :=
  Noncongruent reps n ∧ ∀ a : Int, ∃ r : Int, r ∈ reps ∧ a ≡ r [MOD (n : Int)]

theorem complete_representative_unique (reps : List Int) (n : Nat)
    (h : CompleteResidues reps n) (a : Int) :
    ∃ r : Int, r ∈ reps ∧ a ≡ r [MOD (n : Int)] ∧
      ∀ s ∈ reps, a ≡ s [MOD (n : Int)] → s=r := by
  /-
  Lemma: A complete residue system represents each integer exactly once.
  Proof: Completeness supplies a representative r. If s also represents
  a, symmetry and transitivity give s congruent to r. Distinct entries
  of the system cannot be congruent, so s=r. QED

  Finite sets are represented by lists without repeated entries. The
  definition of completeness combines coverage with uniqueness modulo n;
  it imposes no ordering or bounds on the chosen integer representatives.
  -/
  rcases h.2 a with ⟨r,hr,har⟩
  refine ⟨r,hr,har,?_⟩
  intro s hs has
  exact h.1.2 s hs r hr (modeq_trans s a r n (modeq_symm a s n has) har)


theorem labels_distinct (reps : List Int) (n : Nat) (hn : 0 < n)
    (h : Noncongruent reps n) : (reps.map (fun a => canonicalLabel a n)).Nodup := by
  /-
  Lemma: Replacing noncongruent representatives by their canonical
  labels preserves distinctness. Proof: If two labels were equal,
  the corresponding entries would be congruent. The hypothesis would
  make those entries equal, contrary to their distinctness in the list.
  QED
  -/
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem ?_ h.1
  intro a b ha hb hne he
  exact hne (h.2 a ha b hb ((canonicalLabel_eq_iff a b n hn).mp he))


theorem canonicalLabel_self (r n : Nat) (hr : r < n) :
    canonicalLabel (r : Int) n = r := by
  /-
  Lemma: A number from zero through n-1 is already its own canonical
  representative. Proof: Its chosen label has the same congruence and
  lies in the same interval. Bounded congruent representatives are
  equal, proving the assertion. QED
  -/
  have hs := canonicalLabel_spec r n (by omega)
  have he := bounded_congruent_equal r (canonicalLabel r n) n (by omega)
    (by omega) (by omega) (by omega) hs.2
  omega


theorem complete_residues_length (reps : List Int) (n : Nat) (hn : 0 < n)
    (h : CompleteResidues reps n) : reps.length=n := by
  /-
  Theorem: Every complete residue system modulo n contains n elements.
  Proof: Replace each representative by its canonical label. The labels
  are distinct and belong to 0,...,n-1, so there are at most n.
  Conversely, completeness represents every number in 0,...,n-1.
  The representative of r must have label r, so all n labels occur.
  The elementary bound for distinct lists gives the reverse inequality.
  Mapping labels preserves length, and the two inequalities give n.
  QED
  -/
  let labels := reps.map (fun a => canonicalLabel a n)
  have hnd : labels.Nodup := labels_distinct reps n hn h.1
  have hsub : ∀ r ∈ labels, r ∈ List.range n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨a,_,he⟩
    apply List.mem_range.mpr
    have hs := canonicalLabel_spec a n hn
    omega
  have hreverse : ∀ r ∈ List.range n, r ∈ labels := by
    intro r hr
    have hrn := List.mem_range.mp hr
    rcases h.2 r with ⟨a,ha,hra⟩
    have he := (canonicalLabel_eq_iff r a n hn).mpr hra
    rw [canonicalLabel_self r n hrn] at he
    exact List.mem_map.mpr ⟨a,ha,he.symm⟩
  have hle := distinct_length_bound labels (List.range n) hnd hsub
  have hge := distinct_length_bound (List.range n) labels (List.nodup_range n) hreverse
  simp only [labels,List.length_map,List.length_range] at hle hge
  omega


theorem noncongruent_full_length_complete (reps : List Int) (n : Nat) (hn : 0 < n)
    (h : Noncongruent reps n) (hlen : reps.length=n) : CompleteResidues reps n := by
  /-
  Theorem: Any n pairwise noncongruent integers form a complete
  residue system modulo n.
  Proof: Their canonical labels are n distinct members of 0,...,n-1.
  If a label were missing, adjoining it would give n+1 distinct
  members of a list with only n entries, contradicting the counting
  bound. Thus the canonical label of any integer a occurs. Its
  corresponding representative is congruent to a. This proves coverage;
  noncongruence already gives uniqueness. QED
  -/
  refine ⟨h,?_⟩
  intro a
  let labels := reps.map (fun b => canonicalLabel b n)
  have hnd : labels.Nodup := labels_distinct reps n hn h
  have hsub : ∀ r ∈ labels, r ∈ List.range n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨b,_,he⟩
    apply List.mem_range.mpr
    have hb := canonicalLabel_spec b n hn
    omega
  have hmem : canonicalLabel a n ∈ labels := by
    apply Classical.byContradiction
    intro hnot
    have hmore : (canonicalLabel a n :: labels).Nodup := List.nodup_cons.mpr ⟨hnot,hnd⟩
    have hmoreSub : ∀ r ∈ canonicalLabel a n :: labels, r ∈ List.range n := by
      intro r hr
      rcases List.mem_cons.mp hr with he | ht
      · subst r
        exact List.mem_range.mpr (canonicalLabel_spec a n hn).1
      · exact hsub r ht
    have hb := distinct_length_bound (canonicalLabel a n :: labels) (List.range n) hmore hmoreSub
    simp only [List.length_cons,List.length_range,labels,List.length_map,hlen] at hb
    omega
  rcases List.mem_map.mp hmem with ⟨b,hb,he⟩
  exact ⟨b,hb,(canonicalLabel_eq_iff a b n hn).mp he.symm⟩

end NumberTheory.PolynomialResidues
