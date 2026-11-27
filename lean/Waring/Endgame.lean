import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact exponent arithmetic for the two Waring endgames

These theorems do not assert any smooth mean-value estimate. They verify the
Hölder weights and exponents which must be supplied to the analytic endgame.
The values are the finite rational outputs of the frozen 22 November 2026
certificates. `Certificate*.lean` separately checks their derivation.
-/

noncomputable section

namespace Waring.Endgame

def delta8_32 : ℝ := 178844726003 / 1000000000000
def delta8_34 : ℝ := 117131705619 / 1000000000000
def delta9_38 : ℝ := 185097318519 / 1000000000000
def delta9_40 : ℝ := 135472843760 / 1000000000000

def minorExponent8 (d32 d34 : ℝ) : ℝ :=
  63 / 9 + (24 + d32) / 9 + 7 * (26 + d34) / 9

def minorExponent9 (d38 d40 : ℝ) : ℝ :=
  11 * 80 / 90 + 5 * (29 + d38) / 90 + 74 * (31 + d40) / 90

theorem holder8_weights :
    (1 / 9 : ℝ) + 1 / 9 + 7 / 9 = 1 ∧
    (0 : ℝ) < 1 / 9 ∧ (0 : ℝ) < 7 / 9 ∧
    (72 : ℝ) * (1 / 9) = 8 ∧
    (32 : ℝ) * (1 / 9) + 34 * (7 / 9) = 30 := by
  norm_num

theorem holder9_weights :
    (11 / 90 : ℝ) + 5 / 90 + 74 / 90 = 1 ∧
    (0 : ℝ) < 11 / 90 ∧ (0 : ℝ) < 5 / 90 ∧ (0 : ℝ) < 74 / 90 ∧
    (90 : ℝ) * (11 / 90) = 11 ∧
    (38 : ℝ) * (5 / 90) + 40 * (74 / 90) = 35 := by
  norm_num

theorem minor8_identity (d32 d34 : ℝ) :
    minorExponent8 d32 d34 = 30 + (d32 + 7 * d34 - 1) / 9 := by
  unfold minorExponent8
  ring

theorem minor9_identity (d38 d40 : ℝ) :
    minorExponent9 d38 d40 = 37 + (5 * d38 + 74 * d40 - 11) / 90 := by
  unfold minorExponent9
  ring

theorem exact8_margin :
    delta8_32 + 7 * delta8_34 - 1 = -(154166833 / 125000000000 : ℝ) := by
  norm_num [delta8_32, delta8_34]

theorem exact9_margin :
    5 * delta9_38 + 74 * delta9_40 - 11 = -(9904593833 / 200000000000 : ℝ) := by
  norm_num [delta9_38, delta9_40]

theorem exact8_coarse_bounds :
    delta8_32 ≤ 1789 / 10000 ∧ delta8_34 ≤ 11721 / 100000 := by
  norm_num [delta8_32, delta8_34]

theorem exact9_coarse_bounds :
    delta9_38 ≤ 1851 / 10000 ∧ delta9_40 ≤ 271 / 2000 := by
  norm_num [delta9_38, delta9_40]

theorem minor8_coarse_bound {d32 d34 : ℝ}
    (h32 : d32 ≤ 1789 / 10000) (h34 : d34 ≤ 11721 / 100000) :
    minorExponent8 d32 d34 ≤ 30 - 7 / 100000 := by
  rw [minor8_identity]
  linarith

theorem minor9_coarse_bound {d38 d40 : ℝ}
    (h38 : d38 ≤ 1851 / 10000) (h40 : d40 ≤ 271 / 2000) :
    minorExponent9 d38 d40 ≤ 37 - 19 / 36000 := by
  rw [minor9_identity]
  linarith

theorem minor8_exact_bound :
    minorExponent8 delta8_32 delta8_34 ≤ 30 - 7 / 100000 :=
  minor8_coarse_bound exact8_coarse_bounds.1 exact8_coarse_bounds.2

theorem minor9_exact_bound :
    minorExponent9 delta9_38 delta9_40 < 37 - 1 / 2000 := by
  have h := minor9_coarse_bound exact9_coarse_bounds.1 exact9_coarse_bounds.2
  linarith

/-- An explicit budget for the arbitrarily small loss in the eighth-power estimate. -/
theorem minor8_epsilon_budget {ε : ℝ} (hε : ε ≤ 7 / 200000) :
    minorExponent8 delta8_32 delta8_34 + ε ≤ 30 - 7 / 200000 := by
  have h := minor8_exact_bound
  linarith

/-- An explicit budget for the arbitrarily small loss in the ninth-power estimate. -/
theorem minor9_epsilon_budget {ε : ℝ} (hε : ε ≤ 1 / 4000) :
    minorExponent9 delta9_38 delta9_40 + ε < 37 - 1 / 4000 := by
  have h := minor9_exact_bound
  linarith

theorem pruning8_arithmetic :
    (2 / 3 : ℝ) + 1 / 3 = 1 ∧
    (12 : ℝ) * (2 / 3) = 8 ∧ (90 : ℝ) * (1 / 3) = 30 ∧
    (90 - 42 : ℝ) + 34 = 82 ∧
    (4 : ℝ) * (2 / 3) + 82 * (1 / 3) = 30 ∧
    (1 / 8 : ℝ) * (2 / 3) = 1 / 12 := by
  norm_num

theorem pruning9_arithmetic :
    (11 : ℕ) = 9 + 2 ∧ (11 - 9 : ℕ) + 35 = 37 := by
  norm_num

theorem variable_counts_and_source_ranges :
    (8 : ℕ) + 30 = 38 ∧ 4 * 8 ≤ 38 ∧ 72 = 8 * (8 + 1) ∧
    (11 : ℕ) + 35 = 46 ∧ 4 * 9 ≤ 46 ∧ 90 = 9 * (9 + 1) := by
  norm_num

end Waring.Endgame
