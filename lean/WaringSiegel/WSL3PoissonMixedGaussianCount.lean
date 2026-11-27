import WaringSiegel.WSL3PoissonLongThinGaussian

/-!
# Counting actual original long-thin lattice points from Gaussian Poisson

This is the first step from Gaussian summation to the polynomial Fourier
tails needed by the cubic and averaged quadratic estimates.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def originalGaussianBoxFactor (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.exp (2*Real.pi^2*‖(traceFrequency (K:=K)).toContinuousLinearMap‖^2)

theorem originalGaussianBoxFactor_pos : 0 < originalGaussianBoxFactor K := Real.exp_pos _

/-- On the actual thin box the original Gaussian is bounded below by one
fixed positive constant depending only on the trace form of K. -/
theorem originalGaussian_box_lower (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 < H) (p : inverseDifferent K × 𝓞 K)
    (hu : ‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖ ≤ P⁻¹)
    (hv : ‖mixedEmbedding K (p.2:K)‖ ≤ P*H) :
    1 ≤ originalGaussianBoxFactor K * longThinOriginalGaussian θ P H p := by
  let c := ‖(traceFrequency (K:=K)).toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg _
  have hPu : P * ‖traceFrequency (mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K))‖ ≤ c := by
    calc
      _ ≤ P * (c*P⁻¹) := mul_le_mul_of_nonneg_left
        ((traceFrequency (K:=K)).toContinuousLinearMap.le_opNorm_of_le hu) hP.le
      _ = c := by field_simp
  have hPv : (P*H)⁻¹ * ‖traceFrequency (mixedEmbedding K (p.2:K))‖ ≤ c := by
    calc
      _ ≤ (P*H)⁻¹ * (c*(P*H)) := mul_le_mul_of_nonneg_left
        ((traceFrequency (K:=K)).toContinuousLinearMap.le_opNorm_of_le hv) (by positivity)
      _ = c := by field_simp
  have hu2 := pow_le_pow_left₀ (by positivity) hPu 2
  have hv2 := pow_le_pow_left₀ (by positivity) hPv 2
  rw [mul_pow] at hu2 hv2
  have hQ :
      P^2 * ‖traceFrequency (mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K))‖^2 +
        (P*H)⁻¹^2 * ‖traceFrequency (mixedEmbedding K (p.2:K))‖^2 ≤ 2*c^2 := by linarith
  unfold originalGaussianBoxFactor longThinOriginalGaussian
  rw [← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  change 0 ≤ 2*Real.pi^2*c^2 + _
  nlinarith [mul_le_mul_of_nonneg_left hQ (sq_nonneg Real.pi)]

/-- Every finite actual thin-box count is bounded by the proved full Gaussian sum. -/
theorem originalThinBox_card_le_gaussian (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 < H) (S : Finset (inverseDifferent K × 𝓞 K))
    (hu : ∀ p ∈ S, ‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖ ≤ P⁻¹)
    (hv : ∀ p ∈ S, ‖mixedEmbedding K (p.2:K)‖ ≤ P*H) :
    (S.card:ℝ) ≤ originalGaussianBoxFactor K *
      (∑' p : inverseDifferent K × 𝓞 K, longThinOriginalGaussian θ P H p) := by
  have hs := (longThin_gaussian_summable θ P H hP.ne' hH.ne').2.mul_left
    (originalGaussianBoxFactor K)
  calc
    _ = ∑ _p ∈ S, (1:ℝ) := by simp
    _ ≤ ∑ p ∈ S, originalGaussianBoxFactor K * longThinOriginalGaussian θ P H p := by
      apply Finset.sum_le_sum
      intro p hp
      exact originalGaussian_box_lower θ P H hP hH p (hu p hp) (hv p hp)
    _ ≤ ∑' p : inverseDifferent K × 𝓞 K,
        originalGaussianBoxFactor K * longThinOriginalGaussian θ P H p :=
      hs.sum_le_tsum S (fun p hp => mul_nonneg originalGaussianBoxFactor_pos.le (Real.exp_pos _).le)
    _ = _ := tsum_mul_left

def originalThinMinorConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  originalGaussianBoxFactor K *
    (2*longThinGaussianFactor K*longThinDualConstant (inverseDifferent K)) /
      ((4:ℝ)^nrComplexPlaces K*Real.pi^(finrank ℚ K))

theorem originalThinMinorConstant_pos : 0 < originalThinMinorConstant K := by
  have hC := originalGaussianBoxFactor_pos (K:=K)
  have hG : 0 < longThinGaussianFactor K := Real.exp_pos _
  have hD := longThinDualConstant_pos (inverseDifferent K) inverseDifferent_ne_zero
  unfold originalThinMinorConstant
  positivity

theorem originalThinBox_minor_card_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ))
    (S : Finset (inverseDifferent K × 𝓞 K))
    (hu : ∀ p ∈ S, ‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖ ≤ P⁻¹)
    (hv : ∀ p ∈ S, ‖mixedEmbedding K (p.2:K)‖ ≤ P*H) :
    (S.card:ℝ) ≤ originalThinMinorConstant K * H^(finrank ℚ K) := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  apply (originalThinBox_card_le_gaussian θ P H hPp hHp S hu hv).trans
  have h := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_minor_bound θ P H hP hH hPH hminor).2
    (originalGaussianBoxFactor_pos (K:=K)).le
  exact h.trans_eq (by unfold originalThinMinorConstant; ring)

end WaringSiegel.WSL3Poisson
