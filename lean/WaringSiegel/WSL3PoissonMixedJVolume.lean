import WaringSiegel.WSL3PoissonMixedJPairBound
import WaringSiegel.WSL3PoissonMixedTrivial

/-! # J in volume variables, with its remaining major fourth integral explicit

This is an estimate of the original literal integral, not a replacement
model. The only still-unestimated term displayed in the conclusion is the
actual major fourth moment of the excluded-zero h-sum.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactMixedJIntegral_volume_bound {u w v : mixedSpace K → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (hus : ∀ x, u x ≠ 0 → ‖x‖ ≤ 1)
    (hw : Continuous w) (hwc : HasCompactSupport w) (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C₀ C₁ C₂ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (H M R : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M) (hR : 1 ≤ R),
      ‖compactMixedJIntegral u w v huc hwc hvc H M R (by linarith) (by linarith) (by linarith)‖ ≤
        C₀*(H^finrank ℚ K)*(M^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+δ) +
        C₁*(M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^(2+δ) +
        C₂*(M^finrank ℚ K)^2*(nonzeroCubicMajorFourth u huc H (by linarith))^((1:ℝ)/4)*
          (R^finrank ℚ K : ℝ)^((9:ℝ)/4+δ) := by
  obtain ⟨Cd,hCd,hd⟩ := mixedKIntegral_trivial_volume_bound hu.continuous huc hus hv hvc hvs hδ
  obtain ⟨Cm,hCm,hm⟩ := mixedKMinorIntegral_bound hu huc hus hv hvc hvs hε hδ
  obtain ⟨Ca,hCa,ha⟩ := mixedKMajorIntegral_volume_bound huc hv hvc hvs hδ
  obtain ⟨W,hW⟩ := hw.bounded_above_of_compact_support hwc
  let V := |W|+1
  have hV : 0 < V := by dsimp [V]; positivity
  have hwV (x : mixedSpace K) : ‖w x‖ ≤ V :=
    (hW x).trans ((le_abs_self W).trans (by dsimp [V]; linarith))
  let Cb : ℝ := 2*3^finrank ℚ K
  have hCb : 0 < Cb := by dsimp [Cb]; positivity
  refine ⟨V^2*6*Cb*Cd,V^2*Cb^2*Cm,V^2*Cb^2*Ca,
    by positivity,by positivity,by positivity,fun H M R hH hM hR => ?_⟩
  have hH0 : 0 < H := by linarith
  have hM0 : 0 < M := by linarith
  have hR0 : 0 < R := by linarith
  let T := H^finrank ℚ K
  let Y := M^finrank ℚ K
  let Z := R^finrank ℚ K
  let A := Cd*T*Z^(2+δ)
  let B := Cm*T^((3:ℝ)/4+ε)*Z^(2+δ)+
    Ca*(nonzeroCubicMajorFourth u huc H hH0.ne')^((1:ℝ)/4)*Z^((9:ℝ)/4+δ)
  have hT : 0 < T := by dsimp [T]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hmajor : 0 ≤ nonzeroCubicMajorFourth u huc H hH0.ne' := nonzeroCubicMajorFourth_nonneg _ _ _ _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hzero : mixedKIntegral u v huc hvc H R hH0.ne' hR0.ne' 0 ≤ A := hd H R hH hR 0
  have hoff : ∀ d : 𝓞 K, d ≠ 0 → mixedKIntegral u v huc hvc H R hH0.ne' hR0.ne' d ≤ B := by
    intro d hdn
    rw [mixedKIntegral_eq_major_add_minor u v huc hvc H R hH0 hR0.ne' d]
    exact (add_le_add (ha H R hH0 hR d hdn) (hm H R hH hR d)).trans_eq (by dsimp [B,T,Z]; ring)
  have hj := compactMixedJIntegral_pair_cost_bound u w v huc hwc hvc H M R
    hH0.ne' hM0.ne' hR0.ne' V A B hV.le hA hB hwV hzero hoff
  let N : ℝ := (compactIntegerSupport w hwc M hM0.ne').card
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hN : N ≤ Cb*Y := compactIntegerSupport_card_volume_bound hwc hws M hM
  calc
    _ ≤ V^2*(6*N*A+N^2*B) := hj
    _ ≤ V^2*(6*(Cb*Y)*A+(Cb*Y)^2*B) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg V)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) hA
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hN0 hN 2) hB
    _ = _ := by dsimp [A,B,T,Y,Z]; ring

end WaringSiegel.WSL3Poisson
