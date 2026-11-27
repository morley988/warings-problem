import Mathlib.Tactic

/-! # Coefficient costs for the prime-power local Waring bounds

The finite Witt module uses one coefficient of length a+1 and, for
1 ≤ s ≤ a, exactly 2*p^(a-s) coefficients of length s. The theorems
compute the cost of these coefficients and the a+1 reserved chart variables.
-/

namespace WaringLinear.LocalWordCost

/-- The geometric sum appearing in the Witt truncation lengths. -/
def geoSum (p n : ℕ) := ∑ j ∈ Finset.range n, p^j

/-- Length of the weighted pure-power module when the residual Witt length
is n+1. The second differences give the ambient cyclic multiplicities. -/
def pureLength (p n : ℕ) := ∑ j ∈ Finset.range (n+1), ((n-j)*p^j + 1 + geoSum p j)

theorem pureLength_step (p n : ℕ) :
    pureLength p (n+1) = pureLength p n + 2 * geoSum p (n+1) + 1 := by
  unfold pureLength
  rw [Finset.sum_range_succ (fun j => (n+1-j)*p^j + 1 + geoSum p j) (n+1)]
  have he : ∑ j ∈ Finset.range (n+1), ((n+1-j)*p^j + 1 + geoSum p j) =
      (∑ j ∈ Finset.range (n+1), ((n-j)*p^j + 1 + geoSum p j)) + geoSum p (n+1) := by
    unfold geoSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hle := Finset.mem_range.mp hj
    have hh : n+1-j=(n-j)+1 := by omega
    rw [hh, Nat.add_mul]
    omega
  rw [he]
  simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add]
  omega

theorem pureLength_second_difference (p n : ℕ) :
    pureLength p (n+2) + pureLength p n = 2*pureLength p (n+1) + 2*p^(n+1) := by
  rw [pureLength_step p (n+1), pureLength_step p n]
  have hgeo : geoSum p (n+2) = geoSum p (n+1) + p^(n+1) := Finset.sum_range_succ _ _
  rw [hgeo]
  omega

/-- Cost of all cyclic factors except the unique factor of largest length. -/
def shorterCost (digit : ℕ → ℕ) (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | a+1 => p * shorterCost digit p a + 2 * digit (a+1)

/-- Total scalar coefficient cost in the ambient module. -/
def ambientCost (digit : ℕ → ℕ) (p a : ℕ) :=
  digit (a+1) + shorterCost digit p a

theorem shorterCost_eq_sum (digit : ℕ → ℕ) (p a : ℕ) :
    shorterCost digit p a = ∑ s ∈ Finset.range a, 2 * p^(a-1-s) * digit (s+1) := by
  induction a with
  | zero => simp [shorterCost]
  | succ a ih =>
    rw [shorterCost, ih, Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_range.mp hi
      have he : a + 1 - 1 - i = (a - 1 - i) + 1 := by omega
      rw [he, pow_succ]
      ring
    · simp

/-- A single Teichmüller residue digit and a three-term uniformizer. -/
def oneDigit : ℕ → ℕ
  | 0 => 0
  | n+1 => 1 + 3 * oneDigit n

theorem oneDigit_exact (s : ℕ) : 2 * oneDigit s + 1 = 3^s := by
  induction s with
  | zero => decide
  | succ n ih =>
    rw [oneDigit, pow_succ, ← ih]
    ring

theorem oneDigit_step (p a : ℕ) (hp : 7 ≤ p) :
    ambientCost oneDigit p (a+1) + 1 ≤ p * ambientCost oneDigit p a := by
  change 1 + 3 * oneDigit (a+1) + (p*shorterCost oneDigit p a + 2*oneDigit (a+1)) + 1 ≤ _
  unfold ambientCost
  have hpos : 1 ≤ oneDigit (a+1) := by simp [oneDigit]
  nlinarith [Nat.mul_le_mul_right (oneDigit (a+1)) hp]

/-- The sum of the coefficient and chart costs is at most p^a+1 at p ≥ 7. -/
theorem local_cost_prime_ge_seven (p a : ℕ) (hp : 7 ≤ p) :
    ambientCost oneDigit p a + (a+1) ≤ p^a + 1 := by
  have bound : ambientCost oneDigit p a + a ≤ p^a := by
    induction a with
    | zero => simp [ambientCost, oneDigit, shorterCost]
    | succ a ih =>
      have hs := oneDigit_step p a hp
      have hmul := Nat.mul_le_mul_left p ih
      have hpa : a ≤ p*a := Nat.le_mul_of_pos_left a (by omega)
      rw [pow_succ']
      nlinarith
  omega

theorem local_cost_five_exact (a : ℕ) :
    4 * ambientCost oneDigit 5 a + 1 = 5 ^ (a+1) := by
  induction a with
  | zero => decide
  | succ a ih =>
    have hnext : ambientCost oneDigit 5 (a+1) = 5 * ambientCost oneDigit 5 a + 1 := by
      change 1+3*oneDigit (a+1)+(5*shorterCost oneDigit 5 a + 2*oneDigit (a+1)) = _
      unfold ambientCost
      ring
    rw [hnext, pow_succ 5 (a+1), ← ih]
    ring

/-- Uniform block extraction at 5 with three terms for the residue digit
of length two and seven for the chosen element of valuation two. -/
def twoDigit : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => 3 + 7 * twoDigit n

theorem twoDigit_step : ∀ n, twoDigit (n+1) ≤ 3*twoDigit n + 1
  | 0 => by decide
  | 1 => by decide
  | n+2 => by
    change 3 + 7*twoDigit (n+1) ≤ 3*(3+7*twoDigit n) + 1
    have h := twoDigit_step n
    omega

theorem twoDigit_ambient_step (a : ℕ) :
    ambientCost twoDigit 5 (a+1) ≤ 5 * ambientCost twoDigit 5 a + 1 := by
  have h := twoDigit_step (a+1)
  change twoDigit ((a+1)+1) + (5*shorterCost twoDigit 5 a + 2*twoDigit (a+1)) ≤ _
  unfold ambientCost
  omega

/-- The two-digit estimate yields the same p^a+1 width for p=5 and a≥4. -/
theorem local_cost_five_ge_four (a : ℕ) (ha : 4 ≤ a) :
    ambientCost twoDigit 5 a + (a+1) ≤ 5^a + 1 := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    have h := twoDigit_ambient_step a
    rw [pow_succ]
    omega

#print axioms pureLength_step
#print axioms pureLength_second_difference
#print axioms shorterCost_eq_sum
#print axioms oneDigit_exact
#print axioms local_cost_prime_ge_seven
#print axioms local_cost_five_exact
#print axioms twoDigit_step
#print axioms local_cost_five_ge_four

end WaringLinear.LocalWordCost
