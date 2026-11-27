import WaringSiegel.WSL4ArchProductTails
import WaringSiegel.WSL3IdealPoissonCubic

/-! # Actual ideal-coset Poisson identity for the new near-zero product source -/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap ContDiff
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 1000000

def nearZeroPhaseSchwartz (k : ℕ) (β : mixedSpace K) : 𝓢(mixedSpace K,ℂ) :=
  (nearZeroWeight_hasCompactSupport.smul_right
    (f' := fun x : mixedSpace K => archimedeanTraceCharacter β (x^k))).toSchwartzMap
      (nearZeroWeight_contDiff.smul
        ((archimedeanTraceCharacter_contDiff β).comp (contDiff_id.pow k)))

@[simp] theorem nearZeroPhaseSchwartz_apply (k : ℕ) (β x : mixedSpace K) :
    nearZeroPhaseSchwartz k β x = nearZeroWeight x • archimedeanTraceCharacter β (x^k) := rfl

def scaledNearZeroPowerSchwartz (k : ℕ) (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) : 𝓢(mixedSpace K,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (mixedSpace K) P⁻¹ (inv_ne_zero hP)).toContinuousLinearEquiv
      (nearZeroPhaseSchwartz k (P^k • θ))

theorem scaledNearZeroPowerSchwartz_apply (k : ℕ) (P : ℝ) (hP : P ≠ 0) (θ x : mixedSpace K) :
    scaledNearZeroPowerSchwartz k P hP θ x =
      nearZeroWeight (P⁻¹ • x) • archimedeanTraceCharacter θ (x^k) := by
  change nearZeroWeight (P⁻¹ • x) •
    archimedeanTraceCharacter (P^k • θ) ((P⁻¹ • x)^k) = _
  rw [traceCharacter_smul_power_cancel k P hP]

/-- The literal Fourier transform is exactly the scaled twisted cubic integral. -/
theorem traceFourier_scaledNearZeroCubic (P : ℝ) (hP : 0 < P) (θ ξ : mixedSpace K) :
    traceFourier (scaledNearZeroPowerSchwartz 3 P hP.ne' θ) ξ =
      P^(finrank ℚ K) • nearZeroCubicLinearIntegral (P^3 • θ) (-(P • ξ)) := by
  calc
    _ = ∫ x : mixedSpace K, nearZeroWeight (P⁻¹ • x) •
        (archimedeanTraceCharacter (P^3 • θ) ((P⁻¹ • x)^3) *
          archimedeanTraceCharacter (-(P • ξ)) (P⁻¹ • x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change archimedeanTraceCharacter (-ξ) x *
        scaledNearZeroPowerSchwartz 3 P hP.ne' θ x = _
      rw [scaledNearZeroPowerSchwartz_apply,traceCharacter_smul_power_cancel 3 P hP.ne',
        ← smul_neg,traceCharacter_smul_cancel P hP.ne']
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      have hs := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
        (fun x : mixedSpace K => nearZeroWeight x •
          (archimedeanTraceCharacter (P^3 • θ) (x^3)*archimedeanTraceCharacter (-(P • ξ)) x)) hP.le
      simpa only [NumberField.mixedEmbedding.finrank,nearZeroCubicLinearIntegral] using hs

/-- Exact expansion for the actual scaled cubic source with an arbitrary
finite residue weight, including unit masks and complete cubic characters. -/
theorem poisson_nearZeroCubic_residue_weight (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ)
    (P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
      (nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))) =
      (P^(finrank ℚ K)/((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
        (∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K)) *
            nearZeroCubicLinearIntegral (P^3 • θ) (-(P • mixedEmbedding K (ξ:K)))) := by
  have h := poisson_ideal_residue_weight I hI F
    (scaledNearZeroPowerSchwartz 3 P hP.ne' θ)
  simp_rw [scaledNearZeroPowerSchwartz_apply,traceFourier_scaledNearZeroCubic P hP] at h
  simp_rw [mul_smul_comm] at h
  rw [tsum_const_smul'',smul_smul] at h
  simpa only [div_eq_mul_inv,mul_comm,mul_smul_comm] using h

/-- The exact Fourier factors inherit the already proved all-place stationary
bound and arbitrary nonstationary linear-frequency tails. -/
theorem scaledNearZeroCubicFourier_stationary_tail (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 0 < P), ∀ θ ξ : mixedSpace K,
      ‖traceFourier (scaledNearZeroPowerSchwartz 3 P hP.ne' θ) ξ‖ ≤
        (C*P^(finrank ℚ K))/(cubicProductFrequencyWeight (1/3) (P^3 • θ)*
          cubicProductTailWeight (1/2) N (P^3 • θ) (-(P • ξ))) := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubicLinearIntegral_stationary_tail (K:=K) N
  refine ⟨C,hC,fun P hP θ ξ => ?_⟩
  rw [traceFourier_scaledNearZeroCubic P hP,_root_.norm_smul,
    Real.norm_of_nonneg (pow_nonneg hP.le _)]
  have h := mul_le_mul_of_nonneg_left (hb (P^3 • θ) (-(P • ξ))) (pow_nonneg hP.le (finrank ℚ K))
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h

#print axioms poisson_nearZeroCubic_residue_weight
#print axioms scaledNearZeroCubicFourier_stationary_tail
end WaringSiegel.WSL4
