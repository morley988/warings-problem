import Waring.ReciprocalSums
import Waring.DyadicLogLoss
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The uniform logarithmic Fourier-completion kernel

The capped reciprocal kernel is measurable, nonnegative, bounded and integrable
on every finite interval. Its one-period integral is logarithmic. Composition
with any positive integer multiplier has the SAME one-period integral, covering
the second peak required by parity-restricted completion. The kernel bound is
uniform over all intervals whose lengths are at most the common cap N.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Waring.CompletionKernel
open FiniteSpacing

/-- The explicit zero-distance branch retains the length bound at integral
phases instead of using the field's inverse-of-zero convention. -/
def kernel (N : ℕ) (t : ℝ) : ℝ :=
  truncatedReciprocal (1/(N : ℝ)) (integerDistance t)

theorem measurable_integerDistance : Measurable integerDistance := by
  change Measurable (fun t : ℝ => |t-(round t : ℝ)|)
  simp_rw [abs_sub_round_eq_min]
  exact measurable_fract.min (measurable_const.sub measurable_fract)

theorem measurable_kernel (N : ℕ) : Measurable (kernel N) := by
  unfold kernel truncatedReciprocal
  exact Measurable.ite (measurableSet_eq_fun measurable_integerDistance measurable_const)
    measurable_const (measurable_const.min (measurable_const.div measurable_integerDistance))

theorem kernel_nonneg {N : ℕ} (hN : 0 < N) (t : ℝ) : 0 ≤ kernel N t :=
  truncatedReciprocal_nonneg (by positivity) (abs_nonneg _)

theorem kernel_le_cap (N : ℕ) (t : ℝ) : kernel N t ≤ (N : ℝ) := by
  simpa only [one_div_one_div] using truncatedReciprocal_le_cap (1/(N : ℝ)) (integerDistance t)

/-- A common cap works for every shorter geometric sum, including zero-length
sums and integral phases. -/
theorem linearSumBound_le_kernel_of_le (N n : ℕ) (hnN : n ≤ N) (t : ℝ) :
    linearSumBound n t ≤ kernel N t := by
  unfold linearSumBound kernel truncatedReciprocal
  simp only [one_div_one_div]
  split_ifs with hz
  · exact_mod_cast hnN
  · have hd : 0 < integerDistance t := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    exact min_le_min (by exact_mod_cast hnN)
      (div_le_div_of_nonneg_left (by norm_num) hd (by linarith))

theorem kernel_periodic (N : ℕ) : Function.Periodic (kernel N) 1 := by
  intro t
  unfold kernel integerDistance
  congr 1
  rw [round_add_one, Int.cast_add, Int.cast_one]
  congr 1
  ring

/-- Boundedness proves integrability even after any measurable change of phase. -/
theorem kernel_comp_intervalIntegrable {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ)
    (hf : Measurable f) (a b : ℝ) : IntervalIntegrable (fun t => kernel N (f t)) volume a b := by
  constructor <;>
    apply (integrable_const (N : ℝ)).mono' ((measurable_kernel N).comp hf).aestronglyMeasurable <;>
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hN _)]
      exact kernel_le_cap N _)

theorem kernel_intervalIntegrable {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    IntervalIntegrable (kernel N) volume a b :=
  kernel_comp_intervalIntegrable hN id measurable_id a b

/-- The small-distance set in one unit period lies in its two endpoint strips. -/
theorem distance_sublevel_subset (y : ℝ) :
    {t : ℝ | integerDistance t ≤ y} ∩ Set.Ioc 0 1 ⊆
      Set.Icc 0 y ∪ Set.Icc (1-y) 1 := by
  intro t ht
  rcases ht with ⟨hd, ht0, ht1⟩
  change integerDistance t ≤ y at hd
  have hab := abs_le.mp (abs_sub_round t)
  have hlo : (-1 : ℝ) < (round t : ℝ) := by linarith
  have hhi : (round t : ℝ) < 2 := by linarith
  have hloZ : (-1 : ℤ) < round t := by exact_mod_cast hlo
  have hhiZ : round t < (2 : ℤ) := by exact_mod_cast hhi
  have hr : round t=0 ∨ round t=1 := by omega
  rcases hr with hr | hr
  · left
    have hd' : t ≤ y := by
      simpa only [integerDistance, hr, Int.cast_zero, sub_zero, abs_of_nonneg ht0.le] using hd
    exact ⟨ht0.le,hd'⟩
  · right
    have hd' : -(t-1) ≤ y := by
      simpa only [integerDistance, hr, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr ht1)] using hd
    exact ⟨by linarith,ht1⟩

/-- The two peaks together occupy measure at most twice the distance threshold. -/
theorem distance_sublevel_measure {y : ℝ} (hy : 0 ≤ y) :
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) {t | integerDistance t ≤ y} ≤
      ENNReal.ofReal (2*y) := by
  rw [Measure.restrict_apply (measurableSet_le measurable_integerDistance measurable_const)]
  calc
    _ ≤ volume (Set.Icc (0 : ℝ) y ∪ Set.Icc (1-y) 1) :=
      measure_mono (distance_sublevel_subset y)
    _ ≤ volume (Set.Icc (0 : ℝ) y) + volume (Set.Icc (1-y) 1) := measure_union_le _ _
    _ = ENNReal.ofReal (2*y) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      have hid : (1 : ℝ)-(1-y)=y := by ring
      rw [sub_zero,hid,← ENNReal.ofReal_add hy hy]
      congr 1
      ring

private theorem dyadic_term_integral {y : ℝ} (hy : 0 < y) :
    (∫⁻ t, (if integerDistance t ≤ y then ENNReal.ofReal (2/y) else 0)
      ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal 4 := by
  have hs := measurableSet_le measurable_integerDistance (measurable_const (a := y))
  change (∫⁻ t, {t : ℝ | integerDistance t ≤ y}.indicator
    (fun _ => ENNReal.ofReal (2/y)) t ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤ _
  rw [lintegral_indicator_const hs]
  calc
    _ ≤ ENNReal.ofReal (2/y)*ENNReal.ofReal (2*y) :=
      mul_le_mul_left' (distance_sublevel_measure hy.le) _
    _ = ENNReal.ofReal 4 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      norm_num

/-- The finite dyadic majorant integrates to at most four per scale. -/
theorem kernel_lintegral_le_dyadic (N T : ℕ) (hN : 0 < N)
    (hNT : (N : ℝ) ≤ 2^T) :
    (∫⁻ t, ENNReal.ofReal (kernel N t) ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (4*(T+1 : ℕ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : (1 : ℝ) ≤ (1/(N : ℝ))*2^T := by
    calc
      (1 : ℝ) = (1/(N : ℝ))*(N : ℝ) := by field_simp
      _ ≤ (1/(N : ℝ))*2^T := mul_le_mul_of_nonneg_left hNT (by positivity)
  let term : ℕ → ℝ → ℝ≥0∞ := fun j t =>
    if integerDistance t ≤ (1/(N : ℝ))*2^j then
      ENNReal.ofReal (2/((1/(N : ℝ))*2^j)) else 0
  have hterm (j : ℕ) : Measurable (term j) :=
    Measurable.ite (measurableSet_le measurable_integerDistance measurable_const)
      measurable_const measurable_const
  have hpoint (t : ℝ) : ENNReal.ofReal (kernel N t) ≤
      ∑ j ∈ Finset.range (T+1), term j t := by
    have hr := reciprocal_dyadic_majorant T (show 0 < 1/(N : ℝ) by positivity)
      (show 0 ≤ integerDistance t from abs_nonneg _)
      ((abs_sub_round t).trans (by linarith))
    have he := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)] at he
    simpa only [kernel,term,apply_ite,ENNReal.ofReal_zero] using he
  calc
    _ ≤ ∫⁻ t, ∑ j ∈ Finset.range (T+1), term j t ∂volume.restrict (Set.Ioc (0 : ℝ) 1) :=
      lintegral_mono hpoint
    _ = ∑ j ∈ Finset.range (T+1), ∫⁻ t, term j t ∂volume.restrict (Set.Ioc (0 : ℝ) 1) :=
      lintegral_finset_sum _ (fun j _ => hterm j)
    _ ≤ ∑ _j ∈ Finset.range (T+1), ENNReal.ofReal 4 :=
      Finset.sum_le_sum (fun j _ => dyadic_term_integral (by positivity))
    _ = ENNReal.ofReal (4*(T+1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_num [mul_comm]
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num

/-- The actual real one-period integral satisfies the dyadic bound. -/
theorem kernel_integral_le_dyadic (N T : ℕ) (hN : 0 < N) (hNT : (N : ℝ) ≤ 2^T) :
    (∫ t in (0 : ℝ)..1, kernel N t) ≤ 4*(T+1 : ℕ) := by
  have hi := kernel_intervalIntegrable hN 0 1
  have h := kernel_lintegral_le_dyadic N T hN hNT
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
    (Filter.Eventually.of_forall (kernel_nonneg hN))] at h
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

theorem kernel_integral_le_log (N : ℕ) (hN : 0 < N) :
    (∫ t in (0 : ℝ)..1, kernel N t) ≤ 4*(2+Real.log (N : ℝ)/Real.log 2) := by
  have hd := ShortHeightDistribution.dyadic_depth_le_log (a := 1) (Nat.clog 2 N) le_rfl
    (show (0 : ℝ) < N by exact_mod_cast hN)
    (by simpa only [one_mul] using DyadicLogLoss.pow_clog_le_twice N hN)
  exact (kernel_integral_le_dyadic N (Nat.clog 2 N) hN
    (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) N)).trans
      (mul_le_mul_of_nonneg_left hd (by norm_num))

/-- Positive integer dilations preserve the one-period integral exactly.
In particular the parity kernel K_N(2t) has both peaks accounted for. -/
theorem kernel_integral_mul_nat (N m : ℕ) (hN : 0 < N) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, kernel N ((m : ℝ)*t)) =
      ∫ t in (0 : ℝ)..1, kernel N t := by
  have hperiod := (kernel_periodic N).intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (kernel_intervalIntegrable hN)
  have hid : (∫ t in (0 : ℝ)..(m : ℝ), kernel N t) =
      (m : ℝ)*(∫ t in (0 : ℝ)..1, kernel N t) := by
    simpa only [zero_add,zsmul_eq_mul,Int.cast_natCast,mul_one] using hperiod
  rw [intervalIntegral.integral_comp_mul_left _ (by exact_mod_cast hm.ne'),
    mul_zero,mul_one,hid,smul_eq_mul]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem kernel_integral_mul_nat_le_log (N m : ℕ) (hN : 0 < N) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, kernel N ((m : ℝ)*t)) ≤
      4*(2+Real.log (N : ℝ)/Real.log 2) := by
  rw [kernel_integral_mul_nat N m hN hm]
  exact kernel_integral_le_log N hN

#print axioms kernel_integral_le_log
#print axioms kernel_integral_mul_nat
end Waring.CompletionKernel
