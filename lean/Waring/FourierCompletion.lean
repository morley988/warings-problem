import Waring.Orthogonality
import Waring.ReciprocalSums
import Waring.QuadraticModulation
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Exact interval and parity completion with one common modulation

Arbitrary complex coefficient weights are allowed. Restricting their finite
support is exact Fourier coefficient extraction. The interval kernel is
bounded by one common reciprocal majorant; a parity progression uses that
majorant at `2*t`, not at `t`. This preserves one common real modulation for
the entire family before any moment estimate is applied.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Waring.FourierCompletion

/-- The full weighted finite sum with real linear modulation. -/
def modulatedSum (S : Finset ℤ) (w : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, w n * fourier n (t : AddCircle (1 : ℝ))

/-- The Fourier kernel extracting a specified finite set of integer indices. -/
def kernel (T : Finset ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ T, fourier (-n) (t : AddCircle (1 : ℝ))

theorem continuous_modulatedSum (S : Finset ℤ) (w : ℤ → ℂ) :
    Continuous (modulatedSum S w) := by
  exact continuous_finset_sum S (fun n _ => continuous_const.mul
    ((fourier n).continuous.comp (AddCircle.continuous_mk' 1)))

theorem continuous_kernel (T : Finset ℤ) : Continuous (kernel T) :=
  continuous_finset_sum T (fun n _ =>
    (fourier (-n)).continuous.comp (AddCircle.continuous_mk' 1))

theorem interval_integral_character (n : ℤ) :
    (∫ t in (0 : ℝ)..1, fourier n (t : AddCircle (1 : ℝ))) =
      if n = 0 then (1 : ℂ) else 0 := by
  have h := interval_integral_finite_frequency_coefficient ({n} : Finset ℤ) id 0
  split_ifs with hn
  · subst n
    simpa using h
  · simpa [Finset.filter_singleton, hn] using h

/-- Weighted Fourier coefficient extraction, with an arbitrary support. -/
theorem coefficient_extraction (S : Finset ℤ) (w : ℤ → ℂ) (m : ℤ) :
    (∫ t in (0 : ℝ)..1,
      modulatedSum S w t * fourier (-m) (t : AddCircle (1 : ℝ))) =
        if m ∈ S then w m else 0 := by
  have hcont (n : ℤ) : Continuous (fun t : ℝ =>
      (w n * fourier n (t : AddCircle (1 : ℝ))) * fourier (-m) (t : AddCircle (1 : ℝ))) :=
    (continuous_const.mul ((fourier n).continuous.comp (AddCircle.continuous_mk' 1))).mul
      ((fourier (-m)).continuous.comp (AddCircle.continuous_mk' 1))
  unfold modulatedSum
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum (fun n _ => (hcont n).intervalIntegrable 0 1)]
  simp_rw [mul_assoc, ← fourier_add, intervalIntegral.integral_const_mul, interval_integral_character]
  simp only [add_neg_eq_zero, mul_ite, mul_one, mul_zero]
  simp

/-- Exact completion: the extracting kernel is independent of every weight
`w n`, including any coefficient parameter on which those weights depend. -/
theorem exact_completion (S T : Finset ℤ) (hTS : T ⊆ S) (w : ℤ → ℂ) :
    (∑ n ∈ T, w n) =
      ∫ t in (0 : ℝ)..1, modulatedSum S w t * kernel T t := by
  unfold kernel
  simp_rw [Finset.mul_sum]
  have hint (n : ℤ) : IntervalIntegrable (fun t : ℝ =>
      modulatedSum S w t * fourier (-n) (t : AddCircle (1 : ℝ))) volume 0 1 :=
    ((continuous_modulatedSum S w).mul ((fourier (-n)).continuous.comp
      (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finset_sum (fun n _ => hint n)]
  simp_rw [coefficient_extraction]
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos (hTS hn)]

/-- Taking norms after exact completion leaves a single real modulation. -/
theorem completion_norm_bound (S T : Finset ℤ) (hTS : T ⊆ S) (w : ℤ → ℂ) :
    ‖∑ n ∈ T, w n‖ ≤
      ∫ t in (0 : ℝ)..1, ‖modulatedSum S w t‖ * ‖kernel T t‖ := by
  rw [exact_completion S T hTS w]
  simpa only [norm_mul] using intervalIntegral.norm_integral_le_integral_norm
    (f := fun t => modulatedSum S w t * kernel T t) zero_le_one

/-- A finite integer arithmetic progression. A parity interval is the case
of step two, and an ordinary interval has step one. -/
def progression (M d : ℤ) (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun n : ℕ => M + d * (n : ℤ))

theorem fourier_mul_real (d n : ℤ) (t : ℝ) :
    fourier (d * n) (t : AddCircle (1 : ℝ)) =
      fourier n ((d : ℝ) * t : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem norm_kernel (T : Finset ℤ) (t : ℝ) :
    ‖kernel T t‖ = ‖∑ n ∈ T, fourier n (t : AddCircle (1 : ℝ))‖ := by
  unfold kernel
  simp_rw [fourier_neg]
  rw [← map_sum, Complex.norm_conj]

theorem norm_kernel_progression (M d : ℤ) (N : ℕ) (hd : d ≠ 0) (t : ℝ) :
    ‖kernel (progression M d N) t‖ = ‖linearWeylSum N ((d : ℝ) * t)‖ := by
  have hinj : Function.Injective (fun n : ℕ => M + d * (n : ℤ)) := by
    intro n m heq
    have hh := mul_left_cancel₀ hd (add_left_cancel heq)
    exact_mod_cast hh
  rw [norm_kernel]
  unfold progression
  rw [Finset.sum_image (fun n _ m _ heq => hinj heq)]
  simp_rw [fourier_add, fourier_mul_real]
  rw [← Finset.mul_sum, norm_mul, norm_fourier_value, one_mul]
  rfl

/-- The common majorant is exactly the correctly capped reciprocal, with
an explicit value at every integral phase. -/
def majorant (N : ℕ) (t : ℝ) : ℝ :=
  FiniteSpacing.truncatedReciprocal (1 / (N : ℝ)) (integerDistance t)

theorem norm_kernel_progression_le (M d : ℤ) {n N : ℕ} (hd : d ≠ 0)
    (hN : 0 < N) (hnN : n ≤ N) (t : ℝ) :
    ‖kernel (progression M d n) t‖ ≤ majorant N ((d : ℝ) * t) := by
  rw [norm_kernel_progression M d n hd t]
  calc
    _ ≤ linearSumBound n ((d : ℝ) * t) := by
      rw [← norm_shiftedLinearWeylSum 0]
      exact norm_shiftedLinearWeylSum_le 0 n _
    _ ≤ linearSumBound N ((d : ℝ) * t) := QuadraticModulation.linearSumBound_mono hnN _
    _ ≤ _ := ReciprocalSums.linearSumBound_le_truncated hN _

/-- Every bounded parity class is exactly a finite step-two progression.
The first point and length depend only on the interval and residue class. -/
theorem parity_interval_eq_progression (a b r : ℤ) :
    let M := a + (r - a) % 2
    let N := ((b - M) / 2 + 1).toNat
    (Finset.Icc a b).filter (fun n => n % 2 = r % 2) = progression M 2 N := by
  dsimp only
  ext z
  simp only [Finset.mem_filter, Finset.mem_Icc, progression, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hz
    refine ⟨(z - (a + (r - a) % 2)).toNat / 2, ?_, ?_⟩ <;> omega
  · rintro ⟨n, hn, rfl⟩
    omega

/-- Ordinary bounded integer intervals are the step-one case. -/
theorem interval_eq_progression (a b : ℤ) :
    Finset.Icc a b = progression a 1 (b + 1 - a).toNat := by
  ext z
  simp only [Finset.mem_Icc, progression, Finset.mem_image, Finset.mem_range, one_mul]
  constructor
  · intro hz
    refine ⟨(z-a).toNat, ?_, ?_⟩ <;> omega
  · rintro ⟨n, hn, rfl⟩
    omega

/-- An arbitrary common integrable majorant may be inserted after completion. -/
theorem completion_common_majorant (S T : Finset ℤ) (hTS : T ⊆ S)
    (w : ℤ → ℂ) (K : ℝ → ℝ) (hK : IntervalIntegrable K volume 0 1)
    (hkernel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖kernel T t‖ ≤ K t) :
    ‖∑ n ∈ T, w n‖ ≤ ∫ t in (0 : ℝ)..1, K t * ‖modulatedSum S w t‖ := by
  apply (completion_norm_bound S T hTS w).trans
  apply intervalIntegral.integral_mono_on zero_le_one
    (((continuous_modulatedSum S w).norm.mul (continuous_kernel T).norm).intervalIntegrable 0 1)
    (hK.mul_continuousOn (continuous_modulatedSum S w).norm.continuousOn)
  intro t ht
  exact (mul_le_mul_of_nonneg_left (hkernel t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Finite-family completion with one common modulation. The pointwise family
bound is used before integrating, so the proof never selects a separate
modulation for each family member. Nonnegative outside weights are allowed. -/
theorem family_completion_bound {ι : Type*} (s : Finset ι)
    (S : Finset ℤ) (T : ι → Finset ℤ) (w : ι → ℤ → ℂ) (a : ι → ℝ)
    (hTS : ∀ i ∈ s, T i ⊆ S) (ha : ∀ i ∈ s, 0 ≤ a i)
    (K : ℝ → ℝ) (hKi : IntervalIntegrable K volume 0 1)
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ K t)
    (hkernel : ∀ i ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖kernel (T i) t‖ ≤ K t)
    (B : ℝ) (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ s, a i * ‖modulatedSum S (w i) t‖) ≤ B) :
    (∑ i ∈ s, a i * ‖∑ n ∈ T i, w i n‖) ≤ (∫ t in (0 : ℝ)..1, K t) * B := by
  have hi (i : ι) : IntervalIntegrable
      (fun t => K t * (a i * ‖modulatedSum S (w i) t‖)) volume 0 1 :=
    hKi.mul_continuousOn (continuous_const.mul (continuous_modulatedSum S (w i)).norm).continuousOn
  calc
    _ ≤ ∑ i ∈ s, a i * (∫ t in (0 : ℝ)..1, K t * ‖modulatedSum S (w i) t‖) := by
      apply Finset.sum_le_sum
      intro i his
      exact mul_le_mul_of_nonneg_left
        (completion_common_majorant S (T i) (hTS i his) (w i) K hKi (hkernel i his)) (ha i his)
    _ = ∫ t in (0 : ℝ)..1, K t * (∑ i ∈ s, a i * ‖modulatedSum S (w i) t‖) := by
      simp_rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finset_sum (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ ≤ ∫ t in (0 : ℝ)..1, K t * B := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hKi.mul_continuousOn (continuous_finset_sum s (fun i _ =>
          continuous_const.mul (continuous_modulatedSum S (w i)).norm)).continuousOn)
        (hKi.mul_const B)
      intro t ht
      exact mul_le_mul_of_nonneg_left (hB t ht) (hK t ht)
    _ = _ := intervalIntegral.integral_mul_const B _

#print axioms exact_completion
#print axioms norm_kernel_progression_le
#print axioms parity_interval_eq_progression
#print axioms family_completion_bound

end Waring.FourierCompletion
