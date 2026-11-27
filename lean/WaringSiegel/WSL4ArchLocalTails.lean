import WaringSiegel.WSL4ArchProduct

/-! # Arbitrary rapid linear tails for the actual near-zero local factors -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

theorem nearZeroRealCubicIntegral_tail (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      |theta| ≤ cubicTailRadius 1 * |u| →
      |u|^n * ‖nearZeroRealCubicIntegral theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := real_cubic_nonstationary_bound
    (Complex.ofRealCLM.contDiff.comp realNearZeroBump_contDiff)
    (by norm_num : (0:ℝ) ≤ 1) realNearZeroBump_complex_support n
  refine ⟨C,hC,fun theta u ht => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have ht' : |2*Real.pi*theta| ≤ cubicTailRadius 1*|2*Real.pi*u| := by
    rw [abs_mul (2*Real.pi) theta, abs_mul (2*Real.pi) u, abs_of_pos hp]
    nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
  have hu : |u| ≤ |2*Real.pi*u| := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [abs_nonneg u]
  rw [nearZeroRealCubicIntegral_eq,realCubicTraceIntegral]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg u) hu n) (norm_nonneg _)).trans
    (hb _ _ ht')

theorem nearZeroComplexCubicIntegral_tail (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ, 1 ≤ ‖u‖ →
      ‖theta‖ ≤ cubicTailRadius 1 * ‖u‖ →
      ‖u‖^n * ‖nearZeroComplexCubicIntegral theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complex_cubic_nonstationary_bound
    (Complex.ofRealCLM.contDiff.comp complexNearZeroBump_contDiff)
    (by norm_num : (0:ℝ) ≤ 1) complexNearZeroBump_complex_support n
  refine ⟨C,hC,fun theta u hu ht => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hn (z : ℂ) : ‖(2*Real.pi:ℂ)*z‖ = (2*Real.pi)*‖z‖ := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have ht' : ‖(2*Real.pi:ℂ)*theta‖ ≤ cubicTailRadius 1*‖(2*Real.pi:ℂ)*u‖ := by
    simp only [hn]
    nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
  have huu : ‖u‖ ≤ ‖(2*Real.pi:ℂ)*u‖ := by rw [hn]; nlinarith [norm_nonneg u]
  rw [nearZeroComplexCubicIntegral_eq,complexCubicTraceIntegral]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg u) huu n) (norm_nonneg _)).trans
    (hb _ _ (hu.trans huu) ht')

theorem nearZeroRealCubicIntegral_norm_le (theta u : ℝ) :
    ‖nearZeroRealCubicIntegral theta u‖ ≤ volume.real (closedBall (0:ℝ) 1) := by
  rw [nearZeroRealCubicIntegral_eq]
  change ‖∫ x, (realNearZeroBump x:ℂ)*realCubicPhase (2*Real.pi*theta) (2*Real.pi*u) x‖ ≤ _
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 1)
  · intro x hx
    apply realNearZeroBump_support
    intro hz
    apply hx
    simp only [hz,Complex.ofReal_zero,zero_mul]
  · intro x
    rw [norm_mul,realCubicPhase_norm,mul_one]
    exact realNearZeroBump_norm_le x

theorem nearZeroComplexCubicIntegral_norm_le (theta u : ℂ) :
    ‖nearZeroComplexCubicIntegral theta u‖ ≤ volume.real (closedBall (0:ℂ) 1) := by
  rw [nearZeroComplexCubicIntegral_eq]
  exact complexCubicOscillatoryIntegral_norm_le complexNearZeroBump_complex_support
    complexNearZeroBump_norm_le _ _


theorem nearZeroRealCubicIntegral_weighted_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      cubicTailWeight 1 n |theta| |u| * ‖nearZeroRealCubicIntegral theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := nearZeroRealCubicIntegral_tail n
  refine ⟨2^n*C+volume.real (closedBall (0:ℝ) 1)+1, by positivity, fun theta u => ?_⟩
  unfold cubicTailWeight
  split_ifs with hreg
  · have hr := cubic_tail_region (abs_nonneg theta) hreg
    have ht := hb theta u hr.2
    have hm := mul_le_mul_of_nonneg_right (one_add_pow_bound hr.1 n)
      (norm_nonneg (nearZeroRealCubicIntegral theta u))
    have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2^n)
    nlinarith [measureReal_nonneg (μ := (volume : Measure ℝ)) (s := closedBall 0 1)]
  · rw [one_mul]
    have hb' := nearZeroRealCubicIntegral_norm_le theta u
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

theorem nearZeroComplexCubicIntegral_weighted_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      cubicTailWeight 1 n ‖theta‖ ‖u‖ * ‖nearZeroComplexCubicIntegral theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := nearZeroComplexCubicIntegral_tail n
  refine ⟨2^n*C+volume.real (closedBall (0:ℂ) 1)+1, by positivity, fun theta u => ?_⟩
  unfold cubicTailWeight
  split_ifs with hreg
  · have hr := cubic_tail_region (norm_nonneg theta) hreg
    have ht := hb theta u hr.1 hr.2
    have hm := mul_le_mul_of_nonneg_right (one_add_pow_bound hr.1 n)
      (norm_nonneg (nearZeroComplexCubicIntegral theta u))
    have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2^n)
    nlinarith [measureReal_nonneg (μ := (volume : Measure ℂ)) (s := closedBall 0 1)]
  · rw [one_mul]
    have hb' := nearZeroComplexCubicIntegral_norm_le theta u
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

#print axioms nearZeroRealCubicIntegral_weighted_bound
#print axioms nearZeroComplexCubicIntegral_weighted_bound
end WaringSiegel.WSL4
