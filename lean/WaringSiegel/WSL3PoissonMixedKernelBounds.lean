import WaringSiegel.WSL3PoissonMixedRadial

/-!
# Closed original long-thin product-kernel bounds

These are the polynomial Fourier kernels used by linear Poisson in cubic
Weyl differencing and the averaged quadratic sum. The original kernel is
defined on actual algebraic integers and the actual inverse different.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def originalLongThinProductConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  (2:ℝ)^(2*finrank ℚ K+2)*2*originalThinMinorConstant K

theorem originalLongThinProductConstant_pos : 0 < originalLongThinProductConstant K := by
  have h := originalThinMinorConstant_pos (K:=K)
  unfold originalLongThinProductConstant
  positivity

theorem originalLongThinProductDecay_minor_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) :
    Summable (fun p : originalLongThinDomain (K:=K) P H => originalLongThinProductDecay θ P p) ∧
      (∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p) ≤
        originalLongThinProductConstant K * H^(finrank ℚ K) := by
  obtain ⟨hs, hb⟩ := originalLongThinProductDecay_summable_bound θ P H (by linarith) (by linarith)
  refine ⟨hs, hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_minor_bound θ P H hP hH hPH hminor).2
    (show 0 ≤ (2:ℝ)^(2*finrank ℚ K+2)*2*originalGaussianBoxFactor K by
      have hF := originalGaussianBoxFactor_pos (K:=K); positivity)
  convert h using 1
  · ring
  · unfold originalLongThinProductConstant originalThinMinorConstant
    ring

theorem originalLongThinProductDecay_major_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (γ : K) (hmaj : θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (P^finrank ℚ K) γ) :
    Summable (fun p : originalLongThinDomain (K:=K) P H => originalLongThinProductDecay θ P p) ∧
      (∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p) ≤
        originalLongThinProductConstant K * H^(finrank ℚ K) *
          longThinMajorFactor (inverseDifferent K) θ P H γ := by
  obtain ⟨hs, hb⟩ := originalLongThinProductDecay_summable_bound θ P H (by linarith) (by linarith)
  refine ⟨hs, hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_major_bound θ P H hP hH hPH γ hmaj).2
    (show 0 ≤ (2:ℝ)^(2*finrank ℚ K+2)*2*originalGaussianBoxFactor K by
      have hF := originalGaussianBoxFactor_pos (K:=K); positivity)
  convert h using 1
  · ring
  · unfold originalLongThinProductConstant originalThinMinorConstant
    ring

theorem trace_originalLongThinProductDecay_minor_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (k : ℕ) (hk : 0 < k)
    (hminor : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (P^2*H) ((k:ℝ)^finrank ℚ K * P^finrank ℚ K)) :
    Summable (fun p : originalLongThinDomain (K:=K) P H =>
      originalLongThinProductDecay ((k:ℝ) • θ) P p) ∧
      (∑' p : originalLongThinDomain (K:=K) P H,
        originalLongThinProductDecay ((k:ℝ) • θ) P p) ≤
          originalLongThinProductConstant K * H^(finrank ℚ K) := by
  apply originalLongThinProductDecay_minor_bound ((k:ℝ) • θ) P H hP hH hPH
  exact traceMajorArcUnion_smul_nat_preimage (P^2*H) (P^finrank ℚ K)
    (by positivity) θ k hk hminor

end WaringSiegel.WSL3Poisson
