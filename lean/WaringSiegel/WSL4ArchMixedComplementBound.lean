import WaringSiegel.WSL4ArchMixedComplement

/-! # Numerical bound for the literal complementary mixed-sixth integral -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nearZero_compactMixedSComplementIntegral_bound {w g v : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : ∀ x, g x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 ≤ B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P M : ℝ) (hM : 1 ≤ M) (hMP : M^7 ≤ P),
      ‖compactMixedSComplementIntegral nearZeroSchwartz w g v nearZeroSchwartz_majorant.2.1 hwc hgc hvc
        (P/M^3) P M (P/M)
        (by have h := (mixed_scale_range hM hMP).2.1; linarith)
        (by have h := (mixed_scale_range hM hMP).1; linarith)
        (by linarith)
        (by have h := (mixed_scale_range hM hMP).2.2.1; linarith)‖ ≤
      C*(P^finrank ℚ K : ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K : ℝ)^(-(9/2):ℝ) := by
  obtain ⟨C,hC,hb⟩ := nearZero_compactMixedSComplementIntegral_scales_bound hw hwc hws hg hgc hgs
    hv hvc hvs hε B hB hfinite
  refine ⟨3*C,by positivity,fun P M hM hMP => ?_⟩
  have hP := (mixed_scale_range hM hMP).1
  have hXp : 0 < P^finrank ℚ K := pow_pos (by linarith) _
  have hYp : 0 < M^finrank ℚ K := pow_pos (by linarith) _
  have hYX : (M^finrank ℚ K)^7 ≤ P^finrank ℚ K := by
    simpa only [← pow_mul,Nat.mul_comm] using
      pow_le_pow_left₀ (pow_nonneg (by linarith : 0≤M) 7) hMP (finrank ℚ K)
  have hdom := mixed_complement_monomials_domination (P^finrank ℚ K) (M^finrank ℚ K)
    (one_le_pow₀ hP) (one_le_pow₀ hM) hYX
  apply (hb P M hM hMP).trans
  have hh := mul_le_mul_of_nonneg_left hdom (mul_nonneg hC.le (Real.rpow_nonneg hXp.le ε))
  exact hh.trans_eq (by rw [Real.rpow_add hXp]; ring)

#print axioms nearZero_compactMixedSComplementIntegral_bound
end WaringSiegel.WSL4
