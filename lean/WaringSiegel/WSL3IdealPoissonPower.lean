import WaringSiegel.WSL3IdealPoissonCubic

/-! # Exact scaled ideal Poisson for every polynomial power degree -/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- The actual one-root power integral with an arbitrary linear frequency. -/
def smoothPowerLinearIntegral (k : ℕ) (rho R : ℝ) (θ u : mixedSpace K) : ℂ :=
  ∫ x, smoothRootWeight rho R x •
    (archimedeanTraceCharacter θ (x^k)*archimedeanTraceCharacter u x)

/-- The literal Fourier transform is exactly the scaled twisted power integral. -/
theorem traceFourier_scaledSmoothPower (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : 0 < P) (θ ξ : mixedSpace K) :
    traceFourier (scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ) ξ =
      P^(finrank ℚ K) • smoothPowerLinearIntegral k rho R (P^k • θ) (-(P • ξ)) := by
  calc
    _ = ∫ x : mixedSpace K, smoothRootWeight rho R (P⁻¹ • x) •
        (archimedeanTraceCharacter (P^k • θ) ((P⁻¹ • x)^k) *
          archimedeanTraceCharacter (-(P • ξ)) (P⁻¹ • x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change archimedeanTraceCharacter (-ξ) x *
        scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ x = _
      rw [scaledSmoothPowerSchwartz_apply,traceCharacter_smul_power_cancel k P hP.ne',
        ← smul_neg,traceCharacter_smul_cancel P hP.ne']
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      have hs := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
        (fun x : mixedSpace K => smoothRootWeight rho R x •
          (archimedeanTraceCharacter (P^k • θ) (x^k)*archimedeanTraceCharacter (-(P • ξ)) x)) hP.le
      simpa only [NumberField.mixedEmbedding.finrank,smoothPowerLinearIntegral] using hs

/-- Exact expansion for the actual scaled power source with an arbitrary
finite residue weight, including unit masks and complete power characters. -/
theorem poisson_smoothPower_residue_weight (k : ℕ) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ)
    (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
      (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k))) =
      (P^(finrank ℚ K)/((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
        (∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K)) *
            smoothPowerLinearIntegral k rho R (P^k • θ) (-(P • mixedEmbedding K (ξ:K)))) := by
  have h := poisson_ideal_residue_weight I hI F
    (scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ)
  simp_rw [scaledSmoothPowerSchwartz_apply,traceFourier_scaledSmoothPower k rho R hrho hR P hP] at h
  simp_rw [mul_smul_comm] at h
  rw [tsum_const_smul'',smul_smul] at h
  simpa only [div_eq_mul_inv,mul_comm,mul_smul_comm] using h


#print axioms traceFourier_scaledSmoothPower
#print axioms poisson_smoothPower_residue_weight
end WaringSiegel.WSL3Poisson
