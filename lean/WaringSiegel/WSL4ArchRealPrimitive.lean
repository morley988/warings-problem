import WaringSiegel.WSL3UnitRealWeightedStationary

/-!
# Uniform real cubic primitives including the degenerate critical point

Splitting at the reciprocal cubic scale gives the one-third estimate on
every interval, with an arbitrary real linear twist and both cubic signs.
No assumption separates the source interval from zero.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, conj (f x)) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

theorem real_cubic_zero_primitive_pos {s b : ℝ} (hs : 0 < s) (hb : 0 ≤ b)
    (u : ℝ) :
    s * ‖∫ x in (0:ℝ)..b, realCubicPhase (s^3) u x‖ ≤ 10 := by
  have hi := (realCubicPhase_contDiff (s^3) u).continuous
  by_cases hsmall : b ≤ s⁻¹
  · have hlen := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := b) (C := (1:ℝ))
      (fun x _ => (realCubicPhase_norm (s^3) u x).le)
    simp only [one_mul, sub_zero, abs_of_nonneg hb] at hlen
    have h := mul_le_mul_of_nonneg_left (hlen.trans hsmall) hs.le
    rw [mul_inv_cancel₀ hs.ne'] at h
    linarith
  have hsplit : (∫ x in (0:ℝ)..b, realCubicPhase (s^3) u x) =
      (∫ x in (0:ℝ)..s⁻¹, realCubicPhase (s^3) u x) +
      (∫ x in s⁻¹..b, realCubicPhase (s^3) u x) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable 0 s⁻¹) (hi.intervalIntegrable s⁻¹ b)).symm
  have hlen := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := s⁻¹) (C := (1:ℝ))
    (fun x _ => (realCubicPhase_norm (s^3) u x).le)
  simp only [one_mul, sub_zero, abs_of_pos (inv_pos.mpr hs)] at hlen
  have hout := real_cubic_stationary_interval_bound (inv_pos.mpr hs)
    (le_of_not_ge hsmall) (pow_pos hs 3) u
  have hsqrt : Real.sqrt (s^3*s⁻¹) = s := by
    have he : s^3*s⁻¹ = s^2 := by field_simp
    rw [he, Real.sqrt_sq hs.le]
  rw [hsqrt] at hout
  have hsum := (norm_add_le
    (∫ x in (0:ℝ)..s⁻¹, realCubicPhase (s^3) u x)
    (∫ x in s⁻¹..b, realCubicPhase (s^3) u x)).trans (add_le_add hlen hout)
  rw [hsplit]
  have h := mul_le_mul_of_nonneg_left hsum hs.le
  have he : s*(s⁻¹+9/s) = 10 := by field_simp; ring
  rwa [he] at h

theorem realCubicPhase_reflect (theta u x : ℝ) :
    realCubicPhase theta u (-x) = conj (realCubicPhase theta u x) := by
  rw [← realCubicPhase_neg]
  unfold realCubicPhase
  congr 2
  ring

theorem real_cubic_zero_primitive {s : ℝ} (hs : 0 < s) (b u : ℝ) :
    s * ‖∫ x in (0:ℝ)..b, realCubicPhase (s^3) u x‖ ≤ 10 := by
  by_cases hb : 0 ≤ b
  · exact real_cubic_zero_primitive_pos hs hb u
  have h := real_cubic_zero_primitive_pos hs (neg_nonneg.mpr (le_of_not_ge hb)) u
  have he : ‖∫ x in (0:ℝ)..(-b), realCubicPhase (s^3) u x‖ =
      ‖∫ x in (0:ℝ)..b, realCubicPhase (s^3) u x‖ := by
    have hc : (∫ x in (0:ℝ)..(-b), realCubicPhase (s^3) u (-x)) =
        conj (∫ x in (0:ℝ)..(-b), realCubicPhase (s^3) u x) := by
      simp only [realCubicPhase_reflect, intervalIntegral_conj]
    rw [intervalIntegral.integral_comp_neg] at hc
    simp only [neg_neg, neg_zero] at hc
    rw [intervalIntegral.integral_symm] at hc
    have hn := congrArg norm hc
    simpa only [norm_neg, Complex.norm_conj] using hn.symm
  rwa [he] at h

/-- Uniform cancellation on every oriented interval, at a positive cubic scale. -/
theorem real_cubic_primitive_scale {s : ℝ} (hs : 0 < s) (a b u : ℝ) :
    s * ‖∫ x in a..b, realCubicPhase (s^3) u x‖ ≤ 20 := by
  have hf := (realCubicPhase_contDiff (s^3) u).continuous
  have he : (∫ x in a..b, realCubicPhase (s^3) u x) =
      -(∫ x in (0:ℝ)..a, realCubicPhase (s^3) u x) +
        (∫ x in (0:ℝ)..b, realCubicPhase (s^3) u x) := by
    rw [← intervalIntegral.integral_symm]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable a 0) (hf.intervalIntegrable 0 b)).symm
  have hn := norm_add_le
    (-(∫ x in (0:ℝ)..a, realCubicPhase (s^3) u x))
    (∫ x in (0:ℝ)..b, realCubicPhase (s^3) u x)
  rw [norm_neg] at hn
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hn hs.le
  have ha := real_cubic_zero_primitive hs a u
  have hb := real_cubic_zero_primitive hs b u
  nlinarith

/-- Cubic inverse-third-root cancellation, uniformly in both endpoints and
the arbitrary linear twist. The factor vanishes harmlessly when theta = 0. -/
theorem real_cubic_primitive_one_third (theta a b u : ℝ) :
    |theta|^((1:ℝ)/3) * ‖∫ x in a..b, realCubicPhase theta u x‖ ≤ 20 := by
  have hpositive (t : ℝ) (ht : 0 < t) (v : ℝ) :
      t^((1:ℝ)/3) * ‖∫ x in a..b, realCubicPhase t v x‖ ≤ 20 := by
    have hs : 0 < t^((1:ℝ)/3) := Real.rpow_pos_of_pos ht _
    have he : (t^((1:ℝ)/3))^3 = t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
    simpa only [he] using real_cubic_primitive_scale hs a b v
  rcases lt_trichotomy theta 0 with ht | he | ht
  · have h := hpositive (-theta) (neg_pos.mpr ht) (-u)
    have hc : (∫ x in a..b, realCubicPhase (-theta) (-u) x) =
        conj (∫ x in a..b, realCubicPhase theta u x) := by
      simp only [realCubicPhase_neg, intervalIntegral_conj]
    rw [hc, Complex.norm_conj] at h
    simpa only [abs_of_neg ht] using h
  · subst theta
    norm_num
  · simpa only [abs_of_pos ht] using hpositive theta ht u

#print axioms real_cubic_primitive_one_third
end WaringSiegel.WSL4

