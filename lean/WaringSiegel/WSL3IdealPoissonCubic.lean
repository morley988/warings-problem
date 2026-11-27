import WaringSiegel.WSL3IdealPoissonComplete
import WaringSiegel.WSL3UnitCubicStationaryProduct

/-!
# Literal ideal Poisson expansion for the scaled smooth cubic source

The finite residue coefficient and the actual archimedean cubic integral
occur in one proved formula, with P^d/(Norm(I)*covol(O_K)) and dual D^-1 I^-1.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceCharacter_smul_power_cancel (k : ℕ) (P : ℝ) (hP : P ≠ 0)
    (θ x : mixedSpace K) :
    archimedeanTraceCharacter (P^k • θ) ((P⁻¹ • x)^k) = archimedeanTraceCharacter θ (x^k) := by
  unfold archimedeanTraceCharacter
  congr 2
  congr 1
  rw [smul_pow,smul_mul_assoc,mul_smul_comm,smul_smul,← mul_pow,mul_inv_cancel₀ hP,one_pow,one_smul]

def scaledSmoothPowerSchwartz (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) : 𝓢(mixedSpace K,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (mixedSpace K) P⁻¹ (inv_ne_zero hP)).toContinuousLinearEquiv
      (smoothRootPhaseSchwartz k rho R hrho hR (P^k • θ))

theorem scaledSmoothPowerSchwartz_apply (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : P ≠ 0) (θ x : mixedSpace K) :
    scaledSmoothPowerSchwartz k rho R hrho hR P hP θ x =
      smoothRootWeight rho R (P⁻¹ • x) • archimedeanTraceCharacter θ (x^k) := by
  change smoothRootWeight rho R (P⁻¹ • x) •
    archimedeanTraceCharacter (P^k • θ) ((P⁻¹ • x)^k) = _
  rw [traceCharacter_smul_power_cancel k P hP]

/-- The literal Fourier transform is exactly the scaled twisted cubic integral. -/
theorem traceFourier_scaledSmoothCubic (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : 0 < P) (θ ξ : mixedSpace K) :
    traceFourier (scaledSmoothPowerSchwartz 3 rho R hrho hR P hP.ne' θ) ξ =
      P^(finrank ℚ K) • smoothCubicLinearIntegral rho R (P^3 • θ) (-(P • ξ)) := by
  calc
    _ = ∫ x : mixedSpace K, smoothRootWeight rho R (P⁻¹ • x) •
        (archimedeanTraceCharacter (P^3 • θ) ((P⁻¹ • x)^3) *
          archimedeanTraceCharacter (-(P • ξ)) (P⁻¹ • x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change archimedeanTraceCharacter (-ξ) x *
        scaledSmoothPowerSchwartz 3 rho R hrho hR P hP.ne' θ x = _
      rw [scaledSmoothPowerSchwartz_apply,traceCharacter_smul_power_cancel 3 P hP.ne',
        ← smul_neg,traceCharacter_smul_cancel P hP.ne']
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      have hs := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
        (fun x : mixedSpace K => smoothRootWeight rho R x •
          (archimedeanTraceCharacter (P^3 • θ) (x^3)*archimedeanTraceCharacter (-(P • ξ)) x)) hP.le
      simpa only [NumberField.mixedEmbedding.finrank,smoothCubicLinearIntegral] using hs

/-- Exact expansion for the actual scaled cubic source with an arbitrary
finite residue weight, including unit masks and complete cubic characters. -/
theorem poisson_smoothCubic_residue_weight (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ)
    (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
      (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))) =
      (P^(finrank ℚ K)/((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
        (∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K)) *
            smoothCubicLinearIntegral rho R (P^3 • θ) (-(P • mixedEmbedding K (ξ:K)))) := by
  have h := poisson_ideal_residue_weight I hI F
    (scaledSmoothPowerSchwartz 3 rho R hrho hR P hP.ne' θ)
  simp_rw [scaledSmoothPowerSchwartz_apply,traceFourier_scaledSmoothCubic rho R hrho hR P hP] at h
  simp_rw [mul_smul_comm] at h
  rw [tsum_const_smul'',smul_smul] at h
  simpa only [div_eq_mul_inv,mul_comm,mul_smul_comm] using h

/-- The exact Fourier factors inherit the already proved all-place stationary
bound and arbitrary nonstationary linear-frequency tails. -/
theorem scaledSmoothCubicFourier_stationary_tail (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 0 < P), ∀ θ ξ : mixedSpace K,
      ‖traceFourier (scaledSmoothPowerSchwartz 3 rho R hrho hR P hP.ne' θ) ξ‖ ≤
        (C*P^(finrank ℚ K))/(cubicProductStationaryWeight (P^3 • θ)*
          cubicProductTailWeight R N (P^3 • θ) (-(P • ξ))) := by
  obtain ⟨C,hC,hb⟩ := smoothCubicLinearIntegral_stationary_tail (K:=K) rho R hrho hR N
  refine ⟨C,hC,fun P hP θ ξ => ?_⟩
  rw [traceFourier_scaledSmoothCubic rho R hrho hR P hP,_root_.norm_smul,
    Real.norm_of_nonneg (pow_nonneg hP.le _)]
  have h := mul_le_mul_of_nonneg_left (hb (P^3 • θ) (-(P • ξ))) (pow_nonneg hP.le (finrank ℚ K))
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h

#print axioms poisson_smoothCubic_residue_weight
#print axioms scaledSmoothCubicFourier_stationary_tail
end WaringSiegel.WSL3Poisson
