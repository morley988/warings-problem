import WaringSiegel.WSL4ArchMixedMajorIntegral
import WaringSiegel.WSL4ArchMixedMajorScales
import WaringSiegel.WSL4ArchMixedComplement

/-! # Numerical major bound at H=P/M³ and R=P/M -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nearZeroMixedSIntegrand_major_integral_bound
    (ε : ℝ) (hε : 0<ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0<B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0<C ∧ ∀ (P M : ℝ) (hM : 1≤M) (hMP : M^7≤P),
      (∫q in (mixedComplementArcs (K:=K) P (P/M^3))ᶜ,
        ‖nearZeroMixedSIntegrand (P/M^3) P M (P/M)
          (by have h := (mixed_scale_range hM hMP).2.1; linarith)
          (by have h := (mixed_scale_range hM hMP).1; linarith) (by linarith)
          (by have h := (mixed_scale_range hM hMP).2.2.1; linarith) q‖ ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K : ℝ)^(-(9/2):ℝ) := by
  let L := (6:ℝ)^finrank ℚ K
  have hL : 1≤L := one_le_pow₀ (by norm_num)
  have hd : 0<(finrank ℚ K:ℝ) := by exact_mod_cast (finrank_pos : 0<finrank ℚ K)
  obtain ⟨C,hC,hb⟩ := nearZeroMixedSIntegrand_major_integral_volume_bound L hL
    ((finrank ℚ K:ℝ)*(ε/2)) (ε/4) (by positivity) (by positivity) B hB hfinite
  refine ⟨C*(2*L^((7:ℝ)/2+ε/2)),by positivity,fun P M hM hMP => ?_⟩
  obtain ⟨hP,hH,hR,hHP,hPH⟩ := mixed_scale_range hM hMP
  have hP0 : 0<P := by linarith
  have hM0 : 0<M := by linarith
  have hH0 : 0<P/M^3 := by linarith
  have hR0 : 0<P/M := by linarith
  have hscale : (P/M)^3=P^2*(P/M^3) := by field_simp <;> ring
  have hvolH : (P/M^3)^finrank ℚ K=P^finrank ℚ K/(M^finrank ℚ K)^3 := by
    rw [div_pow]
    congr 1
    simp only [← pow_mul,Nat.mul_comm]
  have hvolR : (P/M)^finrank ℚ K=P^finrank ℚ K/M^finrank ℚ K := div_pow _ _ _
  have hvolD : (P^2*(P/M^3))^finrank ℚ K=((P/M)^finrank ℚ K)^3 := by
    rw [← hscale]
    simp only [← pow_mul,Nat.mul_comm]
  have hpow : P^((finrank ℚ K:ℝ)*(ε/2))=(P^finrank ℚ K : ℝ)^(ε/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hP0.le]
  have hYX : (M^finrank ℚ K)^7≤P^finrank ℚ K := by
    simpa only [← pow_mul,Nat.mul_comm] using
      pow_le_pow_left₀ (pow_nonneg hM0.le 7) hMP (finrank ℚ K)
  have hh := hb (P/M^3) P M (P/M) hH hP hM hR hHP hPH hscale
  rw [hvolH,hvolD,hvolR,hpow,show 2*(ε/4)=ε/2 by ring] at hh
  apply ((nearZeroMixedSIntegrand_actual_major_integral_le (P/M^3) P M (P/M)
    hH0 hP0 hM0.ne' hR0.ne').trans hh).trans
  have hscaleBound := mixed_major_scale_bound (P^finrank ℚ K) (M^finrank ℚ K) L ε
    (one_le_pow₀ hP) (one_le_pow₀ hM) hL hYX hε.le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscaleBound hC.le

#print axioms nearZeroMixedSIntegrand_major_integral_bound
end WaringSiegel.WSL4
