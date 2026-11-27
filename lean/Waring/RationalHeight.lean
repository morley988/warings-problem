import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Intrinsic rational height

The intrinsic height is the infimum over reduced rational approximants of
`max(q, V*|q*α-a|)`. We prove its lower bound, its Dirichlet upper bound,
and the lifting inequality needed to exclude small-height multiples.
No reciprocal-sum or divisor-counting estimate is assumed in this file.
-/

noncomputable section

namespace Waring.RationalHeight

def cost (V α : ℝ) (r : ℚ) : ℝ :=
  max (r.den : ℝ) (V * |(r.den : ℝ) * α - (r.num : ℝ)|)

def height (V α : ℝ) : ℝ := sInf (Set.range (cost V α))

theorem one_le_cost (V α : ℝ) (r : ℚ) : 1 ≤ cost V α r := by
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  exact hd.trans (le_max_left _ _)

theorem costs_bddBelow (V α : ℝ) : BddBelow (Set.range (cost V α)) :=
  ⟨1, by rintro _ ⟨r, rfl⟩; exact one_le_cost V α r⟩

theorem one_le_height (V α : ℝ) : 1 ≤ height V α := by
  apply le_csInf (Set.range_nonempty (cost V α))
  rintro _ ⟨r, rfl⟩
  exact one_le_cost V α r

theorem height_pos (V α : ℝ) : 0 < height V α :=
  lt_of_lt_of_le zero_lt_one (one_le_height V α)

theorem height_le_cost (V α : ℝ) (r : ℚ) : height V α ≤ cost V α r :=
  csInf_le (costs_bddBelow V α) (Set.mem_range_self r)

theorem denominator_error (α : ℝ) (r : ℚ) :
    |(r.den : ℝ) * α - (r.num : ℝ)| = (r.den : ℝ) * |α - (r : ℝ)| := by
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  calc
    |(r.den : ℝ) * α - (r.num : ℝ)| = |(r.den : ℝ) * (α - (r : ℝ))| := by
      congr 1
      rw [Rat.cast_def]
      field_simp
    _ = (r.den : ℝ) * |α - (r : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.den)]

theorem cost_eq (V α : ℝ) (r : ℚ) :
    cost V α r = max (r.den : ℝ) (V * (r.den : ℝ) * |α - (r : ℝ)|) := by
  simp only [cost, denominator_error, mul_assoc]

/-- Reducing an arbitrary fraction cannot increase either denominator or error. -/
theorem height_le_unreduced {V α : ℝ} (hV : 0 ≤ V) (a : ℤ) {q : ℕ}
    (hq : 0 < q) :
    height V α ≤ max (q : ℝ) (V * |(q : ℝ) * α - (a : ℝ)|) := by
  let r : ℚ := Rat.divInt a (q : ℤ)
  have hdenZ : (r.den : ℤ) ≤ q :=
    Int.le_of_dvd (by exact_mod_cast hq) (Rat.den_dvd a (q : ℤ))
  have hden : (r.den : ℝ) ≤ q := by exact_mod_cast hdenZ
  have hcast : (r : ℝ) = (a : ℝ) / (q : ℝ) := by
    dsimp [r]
    rw [Rat.cast_divInt]
    norm_cast
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have herror : (q : ℝ) * |α - (r : ℝ)| = |(q : ℝ) * α - (a : ℝ)| := by
    calc
      (q : ℝ) * |α - (r : ℝ)| = |(q : ℝ) * (α - (r : ℝ))| := by
        rw [abs_mul, abs_of_pos hqR]
      _ = |(q : ℝ) * α - (a : ℝ)| := by
        congr 1
        rw [hcast]
        field_simp
  apply (height_le_cost V α r).trans
  rw [cost_eq]
  apply max_le_max hden
  calc
    V * (r.den : ℝ) * |α - (r : ℝ)| ≤ V * (q : ℝ) * |α - (r : ℝ)| := by
      gcongr
    _ = V * |(q : ℝ) * α - (a : ℝ)| := by rw [mul_assoc, herror]

/-- Dirichlet approximation gives the exact convenient bound `sqrt V`. -/
theorem height_le_sqrt {V : ℝ} (hV : 1 ≤ V) (α : ℝ) :
    height V α ≤ Real.sqrt V := by
  have hV0 : 0 ≤ V := le_trans zero_le_one hV
  have hs : 0 ≤ Real.sqrt V := Real.sqrt_nonneg V
  have hs2 : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV0
  have hs1 : 1 ≤ Real.sqrt V := by nlinarith
  let n : ℕ := ⌊Real.sqrt V⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hs1
  obtain ⟨r, herr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  apply (height_le_cost V α r).trans
  rw [cost_eq]
  apply max_le
  · exact (show (r.den : ℝ) ≤ n by exact_mod_cast hden).trans (Nat.floor_le hs)
  · have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfloor : Real.sqrt V < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    calc
      V * (r.den : ℝ) * |α - (r : ℝ)| ≤
          V * (r.den : ℝ) * (1 / (((n : ℝ) + 1) * (r.den : ℝ))) := by gcongr
      _ = V / ((n : ℝ) + 1) := by field_simp
      _ ≤ Real.sqrt V := by
        apply (div_le_iff₀ hn1).mpr
        nlinarith

/-- Lifting `a/q` for `h*α` to the possibly unreduced `a/(h*q)` gives
the intrinsic-height lower cutoff used in the short-height distribution. -/
theorem height_mul_lift {V H α : ℝ} (hV : 0 ≤ V) {h : ℕ} (hh : 0 < h)
    (hhH : (h : ℝ) ≤ H) :
    height (H * V) α ≤ H * height V ((h : ℝ) * α) := by
  have hH : 0 < H := lt_of_lt_of_le (by exact_mod_cast hh) hhH
  rw [mul_comm H (height _ _)]
  apply (div_le_iff₀ hH).mp
  apply le_csInf (Set.range_nonempty (cost V ((h : ℝ) * α)))
  rintro _ ⟨r, rfl⟩
  apply (div_le_iff₀ hH).mpr
  have hq : 0 < h * r.den := Nat.mul_pos hh r.pos
  have hb := height_le_unreduced (α := α) (mul_nonneg hH.le hV) r.num hq
  apply hb.trans
  push_cast
  have heq : (h : ℝ) * (r.den : ℝ) * α - (r.num : ℝ) =
      (r.den : ℝ) * ((h : ℝ) * α) - (r.num : ℝ) := by ring
  rw [heq]
  unfold cost
  rw [mul_comm (max _ _) H]
  apply max_le
  · calc
      (h : ℝ) * (r.den : ℝ) ≤ H * (r.den : ℝ) :=
        mul_le_mul_of_nonneg_right hhH (by positivity)
      _ ≤ H * max (r.den : ℝ) (V * |(r.den : ℝ) * ((h : ℝ) * α) - (r.num : ℝ)|) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hH.le
  · calc
      H * V * |(r.den : ℝ) * ((h : ℝ) * α) - (r.num : ℝ)| =
          H * (V * |(r.den : ℝ) * ((h : ℝ) * α) - (r.num : ℝ)|) := by ring
      _ ≤ H * max (r.den : ℝ) (V * |(r.den : ℝ) * ((h : ℝ) * α) - (r.num : ℝ)|) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hH.le

theorem no_short_multiple {V H α Y : ℝ} (hV : 0 ≤ V) {h : ℕ} (hh : 0 < h)
    (hhH : (h : ℝ) ≤ H) (hY : height V ((h : ℝ) * α) ≤ Y) :
    height (H * V) α ≤ H * Y := by
  have hH : 0 ≤ H := le_trans (by positivity) hhH
  exact (height_mul_lift hV hh hhH).trans (mul_le_mul_of_nonneg_left hY hH)

#print axioms height_le_sqrt
#print axioms height_mul_lift

end Waring.RationalHeight
