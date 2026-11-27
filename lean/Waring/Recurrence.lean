import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Order properties of the counted exponent recurrence

The backward recurrence has the form `B + max D C / 2`. We verify its
monotonicity and the quantitative attenuation of terminal errors. These
are purely real inequalities. Their interpretation as estimates for smooth
Weyl sums still requires the efficient-differencing analytic lemmas.
-/

noncomputable section

namespace Waring.Recurrence

def backward (pre diagonal current : ℝ) : ℝ :=
  pre + max diagonal current / 2

theorem backward_mono {p d c p' d' c' : ℝ}
    (hp : p ≤ p') (hd : d ≤ d') (hc : c ≤ c') :
    backward p d c ≤ backward p' d' c' := by
  unfold backward
  exact add_le_add hp (div_le_div_of_nonneg_right (max_le_max hd hc) (by norm_num))

theorem backward_lipschitz (p d c c' : ℝ) :
    |backward p d c - backward p d c'| ≤ |c - c'| / 2 := by
  have h : |max d c - max d c'| ≤ |c - c'| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs c c' d
  calc
    |backward p d c - backward p d c'| = |(max d c - max d c') / 2| := by
      congr 1
      unfold backward
      ring
    _ = |max d c - max d c'| / 2 := by rw [abs_div]; norm_num
    _ ≤ |c - c'| / 2 := div_le_div_of_nonneg_right h (by norm_num)

def runBackward : List (ℝ × ℝ) → ℝ → ℝ
  | [], current => current
  | row :: rows, current => runBackward rows (backward row.1 row.2 current)

theorem runBackward_mono (rows : List (ℝ × ℝ)) {c c' : ℝ} (hc : c ≤ c') :
    runBackward rows c ≤ runBackward rows c' := by
  induction rows generalizing c c' with
  | nil => exact hc
  | cons row rows ih =>
    exact ih (backward_mono le_rfl le_rfl hc)

theorem runBackward_lipschitz (rows : List (ℝ × ℝ)) (c c' : ℝ) :
    |runBackward rows c - runBackward rows c'| ≤ |c - c'| / 2 ^ rows.length := by
  induction rows generalizing c c' with
  | nil => simp [runBackward]
  | cons row rows ih =>
    calc
      |runBackward (row :: rows) c - runBackward (row :: rows) c'| ≤
          |backward row.1 row.2 c - backward row.1 row.2 c'| / 2 ^ rows.length :=
        ih _ _
      _ ≤ (|c - c'| / 2) / 2 ^ rows.length :=
        div_le_div_of_nonneg_right (backward_lipschitz _ _ _ _) (by positivity)
      _ = |c - c'| / 2 ^ (row :: rows).length := by
        simp only [List.length_cons, pow_succ, div_div]
        congr 1
        ring

/-- The first counted step preserves all upper bounds supplied to it. -/
theorem first_step_mono {offset diagonal terminal terminal' : ℝ}
    (h : terminal ≤ terminal') :
    offset + max diagonal terminal ≤ offset + max diagonal terminal' :=
  add_le_add_left (max_le_max le_rfl h) _

/-- Rounding upward cannot invalidate any already established upper bound. -/
theorem upward_rounding_sound {actual raw rounded : ℝ}
    (hraw : actual ≤ raw) (hround : raw ≤ rounded) : actual ≤ rounded :=
  hraw.trans hround

end Waring.Recurrence
