import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # The numerical recurrence in efficient differencing

The index `j` in `edDefect k j` is one less than the half-moment.
The analytic differencing inequality over the ring of integers is a
separate input to the application of this recurrence.
-/

noncomputable section

namespace WaringLinear

/-- The ratio in the repeated polynomial difference. -/
def edRatio (k : ℕ) (x : ℝ) : ℝ := (k - x) / (2 * k)

/-- Exponent carried by a polynomial variable of the indicated degree. -/
def edPolyExponent (k : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => 1 / 2 + edRatio k x * edPolyExponent k x j

/-- One step of the half-moment defect recurrence. -/
def edStep (k : ℕ) (x : ℝ) : ℝ :=
  x - 2 * x / (k + x) * (1 - edRatio k x ^ k)

/-- The defect of the moment of order `2(j+1)`. -/
def edDefect (k : ℕ) : ℕ → ℝ
  | 0 => k - 1
  | j + 1 => edStep k (edDefect k j)

private theorem edRatio_bounds {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : 0 ≤ x) (hxk : x ≤ k) : 0 ≤ edRatio k x ∧ edRatio k x ≤ 1 / 2 := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  unfold edRatio
  constructor
  · exact div_nonneg (sub_nonneg.mpr hxk) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * k)).2
    linarith

theorem edPolyExponent_eq {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    edPolyExponent k x j =
      k / (k + x) + x / (k + x) * edRatio k x ^ j := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hden : (k : ℝ) + x ≠ 0 := by positivity
  induction j with
  | zero =>
    simp only [edPolyExponent, pow_zero, mul_one]
    field_simp
  | succ j ih =>
    rw [edPolyExponent, ih, pow_succ]
    unfold edRatio
    field_simp
    ring

/-- The closed-form defect is exactly the next admissible exponent obtained
by adjoining one polynomial variable on either side. -/
theorem edStep_eq_poly {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    edStep k x = x + 2 * edPolyExponent k x k - 2 := by
  rw [edPolyExponent_eq hk hx]
  unfold edStep
  have hden : (k : ℝ) + x ≠ 0 := by
    have : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  field_simp
  ring

private theorem edStep_bounds {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxk : x ≤ k) :
    0 < edStep k x ∧ edStep k x ≤ x ∧ x - 1 ≤ edStep k x := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) + x := by positivity
  obtain ⟨hra, hrb⟩ := edRatio_bounds hk hx.le hxk
  have hp0 : 0 ≤ edRatio k x ^ k := pow_nonneg hra _
  have hp1 : edRatio k x ^ k ≤ 1 := pow_le_one₀ hra (by linarith)
  have hc0 : 0 ≤ 2 * x / (k + x) := by positivity
  have hc1 : 2 * x / (k + x) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hcx : 2 * x / (k + x) < x := by
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos hx (show 0 < (k : ℝ) + x - 2 by linarith)]
  have hupper : 2 * x / (k + x) * (1 - edRatio k x ^ k) ≤ 2 * x / (k + x) := by
    exact mul_le_of_le_one_right hc0 (by linarith)
  have hlower : 0 ≤ 2 * x / (k + x) * (1 - edRatio k x ^ k) :=
    mul_nonneg hc0 (by linarith)
  unfold edStep
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Positivity and the diagonal range of admissible moment exponents. -/
theorem edDefect_bounds {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    0 < edDefect k j ∧ edDefect k j ≤ k ∧ (k : ℝ) - (j + 1) ≤ edDefect k j := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  induction j with
  | zero =>
    simp only [edDefect, Nat.cast_zero, zero_add]
    exact ⟨by linarith, by linarith, by linarith⟩
  | succ j ih =>
    obtain ⟨hp, hm, hl⟩ := edStep_bounds hk ih.1 ih.2.1
    simp only [edDefect, Nat.cast_succ]
    exact ⟨hp, hm.trans ih.2.1, by linarith [ih.2.2]⟩

theorem edDefect_antitone {k : ℕ} (hk : 2 ≤ k) : Antitone (edDefect k) := by
  apply antitone_nat_of_succ_le
  intro j
  obtain ⟨hp, hm, _⟩ := edDefect_bounds hk j
  exact (edStep_bounds hk hp hm).2.1

private theorem edStep_potential {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxk : x ≤ k) :
    2 * (1 - (1 / 2 : ℝ) ^ k) ≤
      k * (Real.log x - Real.log (edStep k x)) + x - edStep k x := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hden : (k : ℝ) + x ≠ 0 := by positivity
  have hy := (edStep_bounds hk hx hxk).1
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hlog
  obtain ⟨hra, hrb⟩ := edRatio_bounds hk hx.le hxk
  have hpow : edRatio k x ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hra hrb k
  have heq : k * (1 - edStep k x / x) + x - edStep k x =
      2 * (1 - edRatio k x ^ k) := by
    unfold edStep
    field_simp [hx.ne']
    ring
  have hmult := mul_le_mul_of_nonneg_left hlog hk'.le
  linarith

/-- The initial potential is evaluated at the actual diagonal half-moment. -/
theorem edDefect_potential_exact_initial {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    k * Real.log (edDefect k j) + edDefect k j ≤
      k * Real.log ((k:ℝ)-1) + ((k:ℝ)-1) - 2 * (1 - (1/2:ℝ)^k) * j := by
  induction j with
  | zero => simp [edDefect]
  | succ j ih =>
    obtain ⟨hp,hm,_⟩ := edDefect_bounds hk j
    have hs := edStep_potential hk hp hm
    simp only [edDefect,Nat.cast_succ]
    linarith

/-- The logarithmic defect potential falls by at least the same amount at
each differencing step. -/
theorem edDefect_potential {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    k * Real.log (edDefect k j) + edDefect k j ≤
      k * Real.log k + k - 2 * (1 - (1 / 2 : ℝ) ^ k) * j := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  induction j with
  | zero =>
    have hl := Real.log_le_log (show 0 < (k : ℝ) - 1 by linarith)
      (show (k : ℝ) - 1 ≤ k by linarith)
    have hm := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ k by positivity)
    simp only [edDefect, Nat.cast_zero, mul_zero, sub_zero]
    linarith
  | succ j ih =>
    obtain ⟨hp, hm, _⟩ := edDefect_bounds hk j
    have hs := edStep_potential hk hp hm
    simp only [edDefect, Nat.cast_succ]
    linarith

/-- An explicit exponentially decreasing admissible defect. -/
theorem edDefect_le_exp {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    edDefect k j ≤
      k * Real.exp (1 - 2 * (1 - (1 / 2 : ℝ) ^ k) * j / k) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hx := (edDefect_bounds hk j).1
  have hp := edDefect_potential hk j
  have hlog : Real.log (edDefect k j) ≤
      Real.log k + (1 - 2 * (1 - (1 / 2 : ℝ) ^ k) * j / k) := by
    apply (mul_le_mul_iff_right₀ hk').mp
    have hcancel : 2 * (1 - (1 / 2 : ℝ) ^ k) * j / k * k =
        2 * (1 - (1 / 2 : ℝ) ^ k) * j := div_mul_cancel₀ _ hk'.ne'
    linarith
  have h := Real.exp_le_exp.mpr hlog
  simpa only [Real.exp_add, Real.exp_log hx, Real.exp_log hk'] using h

#print axioms edStep_eq_poly
#print axioms edDefect_bounds
#print axioms edDefect_antitone
#print axioms edDefect_potential
#print axioms edDefect_potential_exact_initial
#print axioms edDefect_le_exp

end WaringLinear
