import WaringSiegel.WSL4ArchNonzeroFourth
import WaringSiegel.WSL3PoissonMixedComplementVolume

/-! # Numerical mixed-moment inequalities for the actual near-zero h-source

The major fourth integral has been evaluated and is no longer an analytic
premise. The finite twisted coefficient bound remains explicit.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Function Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nearZero_majorFourth_quarter_bound
    (ε : ℝ) (hε : 0 < ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 ≤ B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ) (hH : 1 ≤ H),
      (nonzeroCubicMajorFourth (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 H
        (by linarith))^((1:ℝ)/4) ≤ C*(H^finrank ℚ K : ℝ)^((1:ℝ)/4+ε) := by
  obtain ⟨C,hC,hb⟩ := nearZero_nonzeroCubicMajorFourth_bound (4*ε) (by positivity) B hB hfinite
  refine ⟨C^((1:ℝ)/4),by positivity,fun H hH => ?_⟩
  have hH0 : 0 < H := by linarith
  apply (Real.rpow_le_rpow (nonzeroCubicMajorFourth_nonneg _ _ _ _) (hb H hH)
    (by norm_num : (0:ℝ) ≤ 1/4)).trans_eq
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg (pow_nonneg hH0.le _) _),
    ← Real.rpow_mul (pow_nonneg hH0.le _)]
  congr 2
  ring

theorem nearZero_compactMixedJIntegral_volume_bound {w v : mixedSpace K → ℂ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 ≤ B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C₀ C₁ C₂ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (H M R : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M) (hR : 1 ≤ R),
      ‖compactMixedJIntegral nearZeroSchwartz w v nearZeroSchwartz_majorant.2.1 hwc hvc
        H M R (by linarith) (by linarith) (by linarith)‖ ≤
        C₀*(H^finrank ℚ K)*(M^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+δ) +
        C₁*(M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^(2+δ) +
        C₂*(M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((1:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^((9:ℝ)/4+δ) := by
  obtain ⟨C0,C1,C2,hC0,hC1,hC2,hj⟩ := compactMixedJIntegral_volume_bound
    nearZeroSchwartz_majorant.1 nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.2.2.2.2
    hw hwc hws hv hvc hvs hε hδ
  obtain ⟨A,hA,ha⟩ := nearZero_majorFourth_quarter_bound ε hε B hB hfinite
  refine ⟨C0,C1,C2*A,hC0,hC1,mul_pos hC2 hA,fun H M R hH hM hR => ?_⟩
  apply (hj H M R hH hM hR).trans
  apply add_le_add_left
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ha H hH) (mul_nonneg hC2.le (sq_nonneg (M^finrank ℚ K))))
    (Real.rpow_nonneg (pow_nonneg (by linarith : 0 ≤ R) (finrank ℚ K)) ((9:ℝ)/4+δ))
  exact h.trans_eq (by ring)

theorem nearZero_compactMixedSComplementIntegral_volume_bound {w g v : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : ∀ x, g x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 ≤ B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H P M R : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P)
      (hM : 1 ≤ M) (hR : 1 ≤ R), H ≤ P → P ≤ H^2 →
      ‖compactMixedSComplementIntegral nearZeroSchwartz w g v nearZeroSchwartz_majorant.2.1 hwc hgc hvc
        H P M R (by linarith) (by linarith) (by linarith) (by linarith)‖^2 ≤
      C*(H^finrank ℚ K)*(P^finrank ℚ K : ℝ)^(1+ε)*(R^finrank ℚ K : ℝ)^(2+ε)*
        ((H^finrank ℚ K)*(M^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+ε) +
        (M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^(2+ε) +
        (M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((1:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^((9:ℝ)/4+ε)) := by
  obtain ⟨C,hC,hb⟩ := compactMixedSComplementIntegral_volume_bound
    nearZeroSchwartz_majorant.1 nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.2.2.2.2
    nearZeroSchwartz_majorant.2.2.2.1 hw hwc hws hg hgc hgs hv hvc hvs hε
  obtain ⟨A,hA,ha⟩ := nearZero_majorFourth_quarter_bound ε hε B hB hfinite
  refine ⟨C*(1+A),by positivity,fun H P M R hH hP hM hR hHP hPH => ?_⟩
  apply (hb H P M R hH hP hM hR hHP hPH).trans
  let T := H^finrank ℚ K
  let Y := M^finrank ℚ K
  let Z := R^finrank ℚ K
  let D := C*T*(P^finrank ℚ K:ℝ)^(1+ε)*Z^(2+ε)
  let a0 := T*Y*Z^(2+ε)
  let a1 := Y^2*T^((3:ℝ)/4+ε)*Z^(2+ε)
  let a2 := Y^2*T^((1:ℝ)/4+ε)*Z^((9:ℝ)/4+ε)
  have hT : 0 ≤ T := pow_nonneg (by linarith) _
  have hY : 0 ≤ Y := pow_nonneg (by linarith) _
  have hZ : 0 ≤ Z := pow_nonneg (by linarith) _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have hm : Y^2*(nonzeroCubicMajorFourth (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 H
      (by linarith))^((1:ℝ)/4)*Z^((9:ℝ)/4+ε) ≤ A*a2 := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ha H hH) (sq_nonneg Y)) (Real.rpow_nonneg hZ _)).trans_eq (by dsimp [a2,T]; ring)
  calc
    _ ≤ D*(a0+a1+A*a2) := mul_le_mul_of_nonneg_left (add_le_add_left hm _) hD
    _ ≤ D*((1+A)*(a0+a1+a2)) := by gcongr; nlinarith
    _ = _ := by dsimp [D,a0,a1,a2,T,Y,Z]; ring

#print axioms nearZero_majorFourth_quarter_bound
#print axioms nearZero_compactMixedJIntegral_volume_bound
#print axioms nearZero_compactMixedSComplementIntegral_volume_bound
end WaringSiegel.WSL4
