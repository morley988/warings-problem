import WaringSiegel.WSL4ArchMixedScales

/-! # The actual complementary mixed-sixth contribution at the intended scales -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem mixed_scale_range {P M : ℝ} (hM : 1 ≤ M) (hMP : M^7 ≤ P) :
    1 ≤ P ∧ 1 ≤ P/M^3 ∧ 1 ≤ P/M ∧ P/M^3 ≤ P ∧ P ≤ (P/M^3)^2 := by
  have hM0 : 0 < M := by linarith
  have hP : 1 ≤ P := (one_le_pow₀ hM).trans hMP
  have hM3P : M^3 ≤ P := (pow_le_pow_right₀ hM (by omega : 3 ≤ 7)).trans hMP
  have hMP' : M ≤ P := (le_self_pow₀ hM (by norm_num : 7 ≠ 0)).trans hMP
  refine ⟨hP,(one_le_div (pow_pos hM0 _)).mpr hM3P,(one_le_div hM0).mpr hMP',
    div_le_self (by linarith) (one_le_pow₀ hM),?_⟩
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos (pow_pos hM0 3) 2)).mpr
  have hM6P : M^6 ≤ P := (pow_le_pow_right₀ hM (by omega : 6 ≤ 7)).trans hMP
  have hh := mul_le_mul_of_nonneg_left hM6P (by linarith : 0 ≤ P)
  convert hh using 1 <;> ring

theorem nearZero_compactMixedSComplementIntegral_scales_bound {w g v : mixedSpace K → ℂ}
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
      C*(P^finrank ℚ K : ℝ)^ε*
        ((P^finrank ℚ K : ℝ)^((7:ℝ)/2)*(M^finrank ℚ K : ℝ)^(-(9/2):ℝ)+
        (P^finrank ℚ K : ℝ)^((13:ℝ)/4)*(M^finrank ℚ K : ℝ)^(-3:ℝ)+
        (P^finrank ℚ K : ℝ)^((27:ℝ)/8)*(M^finrank ℚ K : ℝ)^(-(29/8):ℝ)) := by
  obtain ⟨C,hC,hb⟩ := nearZero_compactMixedSComplementIntegral_volume_bound hw hwc hws hg hgc hgs
    hv hvc hvs (show 0 < ε/2 by positivity) B hB hfinite
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun P M hM hMP => ?_⟩
  obtain ⟨hP,hH,hR,hHP,hPH⟩ := mixed_scale_range hM hMP
  have hvolH : (P/M^3)^finrank ℚ K = P^finrank ℚ K/(M^finrank ℚ K)^3 := by
    rw [div_pow]
    congr 1
    simp only [← pow_mul,Nat.mul_comm]
  have hvolR : (P/M)^finrank ℚ K = P^finrank ℚ K/M^finrank ℚ K := div_pow _ _ _
  have hh := hb (P/M^3) P M (P/M) hH hP hM hR hHP hPH
  rw [hvolH,hvolR] at hh
  apply mixed_complement_scale_sqrt hC (norm_nonneg _) (one_le_pow₀ hP) (one_le_pow₀ hM) hε.le
  simpa only [mul_assoc] using hh

/-- All three complementary monomials are dominated in the actual mixed range. -/
theorem mixed_complement_monomials_domination (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hYX : Y^7 ≤ X) :
    X^((7:ℝ)/2)*Y^(-(9/2):ℝ)+X^((13:ℝ)/4)*Y^(-3:ℝ)+
      X^((27:ℝ)/8)*Y^(-(29/8):ℝ) ≤ 3*(X^((7:ℝ)/2)*Y^(-(9/2):ℝ)) := by
  have hXp : 0 < X := by linarith
  have hYp : 0 < Y := by linarith
  have hY6X : Y^6 ≤ X := (pow_le_pow_right₀ hY (by omega : 6 ≤ 7)).trans hYX
  have h6 : Y^((3:ℝ)/2) ≤ X^((1:ℝ)/4) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hYp.le 6) hY6X (by norm_num : (0:ℝ)≤1/4)
    have he : (Y^6)^((1:ℝ)/4) = Y^((3:ℝ)/2) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hYp.le]
      norm_num
    rwa [he] at hh
  have h7 : Y^((7:ℝ)/8) ≤ X^((1:ℝ)/8) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hYp.le 7) hYX (by norm_num : (0:ℝ)≤1/8)
    have he : (Y^7)^((1:ℝ)/8) = Y^((7:ℝ)/8) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hYp.le]
      norm_num
    rwa [he] at hh
  have hb : X^((13:ℝ)/4)*Y^(-3:ℝ) ≤ X^((7:ℝ)/2)*Y^(-(9/2):ℝ) := by
    have hh := mul_le_mul_of_nonneg_left h6
      (mul_nonneg (Real.rpow_nonneg hXp.le ((13:ℝ)/4)) (Real.rpow_nonneg hYp.le (-(9/2):ℝ)))
    have hl : X^((13:ℝ)/4)*Y^(-(9/2):ℝ)*Y^((3:ℝ)/2) = X^((13:ℝ)/4)*Y^(-3:ℝ) := by
      rw [mul_assoc,← Real.rpow_add hYp]
      norm_num
    have hr : X^((13:ℝ)/4)*Y^(-(9/2):ℝ)*X^((1:ℝ)/4) = X^((7:ℝ)/2)*Y^(-(9/2):ℝ) := by
      calc
        _ = (X^((13:ℝ)/4)*X^((1:ℝ)/4))*Y^(-(9/2):ℝ) := by ring
        _ = _ := by rw [← Real.rpow_add hXp]; norm_num
    rwa [hl,hr] at hh
  have hc : X^((27:ℝ)/8)*Y^(-(29/8):ℝ) ≤ X^((7:ℝ)/2)*Y^(-(9/2):ℝ) := by
    have hh := mul_le_mul_of_nonneg_left h7
      (mul_nonneg (Real.rpow_nonneg hXp.le ((27:ℝ)/8)) (Real.rpow_nonneg hYp.le (-(9/2):ℝ)))
    have hl : X^((27:ℝ)/8)*Y^(-(9/2):ℝ)*Y^((7:ℝ)/8) = X^((27:ℝ)/8)*Y^(-(29/8):ℝ) := by
      rw [mul_assoc,← Real.rpow_add hYp]
      norm_num
    have hr : X^((27:ℝ)/8)*Y^(-(9/2):ℝ)*X^((1:ℝ)/8) = X^((7:ℝ)/2)*Y^(-(9/2):ℝ) := by
      calc
        _ = (X^((27:ℝ)/8)*X^((1:ℝ)/8))*Y^(-(9/2):ℝ) := by ring
        _ = _ := by rw [← Real.rpow_add hXp]; norm_num
    rwa [hl,hr] at hh
  linarith

#print axioms nearZero_compactMixedSComplementIntegral_scales_bound
#print axioms mixed_complement_monomials_domination
end WaringSiegel.WSL4
