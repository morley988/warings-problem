import WaringSiegel.LargeKArithmetic

/-!
# Two-sided numerical bounds for the optimized threshold

For every `k ≥ 64`, the rounded interpolation threshold differs from
`k²-k+2√(2k)` by a bounded numerical amount.  These are theorems about the
explicit rational threshold, not estimates for the Waring–Siegel function.
-/

namespace WaringSiegel.Thresholds

/-- A convenient elementary exponential lower bound for the classical-Hua branch. -/
theorem nine_sq_le_two_pow (j : ℕ) (hj : 16 ≤ j) : 9 * j ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hs : 9 * (j + 1) ^ 2 ≤ 2 * (9 * j ^ 2) := by nlinarith
    calc
      9 * (j + 1)^2 ≤ 2 * (9 * j^2) := hs
      _ ≤ 2 * (2^j) := Nat.mul_le_mul_left 2 ih
      _ = 2^(j+1) := by rw [pow_succ]; omega

/-- All classical-Hua candidates lie above this coarse threshold for `k≥64`. -/
theorem second_lower_large (k j : ℕ) (hk : 64 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (k : ℝ)^2 - k / 2 ≤ (second k j : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hden : (0 : ℝ) < k + 1 - j := by linarith
  have hdiv : ((k : ℝ) * j - (2 : ℝ)^j) / (k + 1 - j) ≤ k / 2 := by
    apply (div_le_iff₀ hden).mpr
    by_cases hsmall : 3 * j ≤ k + 1
    · have hsmall' : 3 * (j : ℝ) ≤ k + 1 := by exact_mod_cast hsmall
      have hmul := mul_nonneg hk0 (sub_nonneg.mpr hsmall')
      have hpow : (0 : ℝ) ≤ 2 ^ j := by positivity
      nlinarith
    · have hj16 : 16 ≤ j := by omega
      have hklt : (k : ℝ) < 3 * j := by exact_mod_cast (show k < 3 * j by omega)
      have hpow : (9 : ℝ) * (j : ℝ)^2 ≤ (2 : ℝ)^j := by
        exact_mod_cast nine_sq_le_two_pow j hj16
      have hmul := mul_nonneg hj0 (sub_nonneg.mpr hklt.le)
      have hnum : (k : ℝ) * j - (2 : ℝ)^j ≤ 0 := by nlinarith
      have hrhs : (0 : ℝ) ≤ (k / 2) * (k + 1 - j) :=
        mul_nonneg (by positivity) hden.le
      exact hnum.trans hrhs
  simpa only [second, Rat.cast_sub, Rat.cast_pow, Rat.cast_mul, Rat.cast_div,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using
    (sub_le_sub_left hdiv ((k : ℝ)^2))

/-- AM–GM in the exact shape required by the reparametrized first branch. -/
theorem two_sqrt_le_add_div (a q : ℝ) (ha : 0 ≤ a) (hq : 0 < q) :
    2 * Real.sqrt a ≤ q + a / q := by
  calc
    2 * Real.sqrt a ≤ (q^2 + a) / q := by
      apply (le_div_iff₀ hq).mpr
      nlinarith [sq_nonneg (q - Real.sqrt a), Real.sq_sqrt ha]
    _ = q + a / q := by field_simp

/-- Every first-branch candidate has the square-root lower bound. -/
theorem first_lower_sqrt (k r : ℕ) (_hr : 1 ≤ r) (hrk : r ≤ k) :
    (k : ℝ)^2 - k - 3 + 2 * Real.sqrt (2 * ((k : ℝ) + 1)) ≤ (first k r : ℝ) := by
  let q : ℝ := (k : ℝ) - r + 1
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hq : 0 < q := by dsimp [q]; linarith
  have ham := two_sqrt_le_add_div (2 * ((k : ℝ) + 1)) q (by positivity) hq
  have heq : (first k r : ℝ) = (k : ℝ)^2 - k - 3 +
      (q + (2 * k + 2) / q) := by
    have hrkQ : (r : ℚ) ≤ k := by exact_mod_cast hrk
    have hqQ : (k : ℚ) - r + 1 ≠ 0 := by linarith
    have hf := first_reparametrized (k : ℚ) ((k : ℚ) - r + 1) hqQ
    have har : (k : ℚ) - ((k : ℚ) - r + 1) + 1 = r := by ring
    rw [har] at hf
    have hfR := congrArg (fun z : ℚ => (z : ℝ)) hf
    simpa only [q, Rat.cast_sub, Rat.cast_pow, Rat.cast_mul, Rat.cast_div,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hfR
  rw [show 2 * ((k : ℝ) + 1) = 2 * k + 2 by ring] at ham ⊢
  rw [heq]
  linarith

/-- The coarse second-branch bound dominates the desired square-root lower bound. -/
theorem sqrt_lower_le_second_lower (k : ℕ) (hk : 64 ≤ k) :
    (k : ℝ)^2 - k - 3 + 2 * Real.sqrt (2 * ((k : ℝ) + 1)) ≤
      (k : ℝ)^2 - k / 2 := by
  have hk' : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul : (0 : ℝ) ≤ k * (k - 64) := mul_nonneg (by positivity) (by linarith)
  have hs : Real.sqrt (2 * ((k : ℝ) + 1)) ≤ (k : ℝ) / 4 + 3 / 2 := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith
  linarith

/-- Lower bounds pass through a finite minimum, including the sentinel. -/
theorem le_cast_foldr_min (xs : List ℚ) (base : ℚ) (a : ℝ)
    (hb : a ≤ (base : ℝ)) (hx : ∀ x ∈ xs, a ≤ (x : ℝ)) :
    a ≤ ((xs.foldr min base : ℚ) : ℝ) := by
  induction xs with
  | nil => exact hb
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [min_def]
    split_ifs
    · exact hx x (by simp)
    · exact ih (fun y hy => hx y (by simp [hy]))

/-- Uniform square-root lower bound for the complete optimized rational threshold. -/
theorem threshold_lower_sqrt (k : ℕ) (hk : 64 ≤ k) :
    (k : ℝ)^2 - k - 3 + 2 * Real.sqrt (2 * ((k : ℝ) + 1)) ≤ (threshold k : ℝ) := by
  unfold threshold
  apply le_cast_foldr_min
  · have hc := sqrt_lower_le_second_lower k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    push_cast
    linarith
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact first_lower_sqrt k (r + 1) (by omega)
        (by have := List.mem_range.mp hr; omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact (sqrt_lower_le_second_lower k hk).trans
        (second_lower_large k (j + 1) hk (by omega)
          (by have := List.mem_range.mp hj; omega))

/-- The strict floor step yields a two-sided explicit bounded remainder. -/
theorem sufficientVariables_two_sided (k : ℕ) (hk : 64 ≤ k) :
    (k : ℝ)^2 - k - 3 + 2 * Real.sqrt (2 * ((k : ℝ) + 1)) <
        (sufficientVariables k : ℝ) ∧
      (sufficientVariables k : ℝ) ≤
        (k : ℝ)^2 - k - 1 + 2 * Real.sqrt (2 * ((k : ℝ) + 1)) := by
  constructor
  · apply (threshold_lower_sqrt k hk).trans_lt
    unfold sufficientVariables
    rw [if_neg (by omega)]
    exact_mod_cast strict_floor_threshold (threshold k)
  · exact sufficientVariables_explicit_upper k (by omega)

/-- A direct bounded-remainder statement with the manuscript's `sqrt(2k)` center. -/
theorem sufficientVariables_bounded_remainder (k : ℕ) (hk : 64 ≤ k) :
    (k : ℝ)^2 - k + 2 * Real.sqrt (2 * (k : ℝ)) - 3 <
        (sufficientVariables k : ℝ) ∧
      (sufficientVariables k : ℝ) ≤ (k : ℝ)^2 - k + 2 * Real.sqrt (2 * (k : ℝ)) := by
  obtain ⟨hl, hu⟩ := sufficientVariables_two_sided k hk
  have hmono : Real.sqrt (2 * (k : ℝ)) ≤ Real.sqrt (2 * ((k : ℝ) + 1)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hk' : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hs0 : 0 ≤ Real.sqrt (2 * (k : ℝ)) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (2 * (k : ℝ)))^2 = 2 * (k : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hslo : (7 : ℝ) / 4 ≤ Real.sqrt (2 * (k : ℝ)) := by nlinarith
  have hdiff : Real.sqrt (2 * ((k : ℝ) + 1)) ≤ Real.sqrt (2 * (k : ℝ)) + 1 / 2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  constructor <;> linarith

/-- For all `k≥64`, the absolute numerical remainder is strictly less than three. -/
theorem sufficientVariables_bounded_error (k : ℕ) (hk : 64 ≤ k) :
    |(sufficientVariables k : ℝ) -
      ((k : ℝ)^2 - k + 2 * Real.sqrt (2 * (k : ℝ)))| < 3 := by
  obtain ⟨hl, hu⟩ := sufficientVariables_bounded_remainder k hk
  apply abs_lt.mpr
  constructor <;> linarith

end WaringSiegel.Thresholds

#print axioms WaringSiegel.Thresholds.sufficientVariables_two_sided
#print axioms WaringSiegel.Thresholds.sufficientVariables_bounded_error
