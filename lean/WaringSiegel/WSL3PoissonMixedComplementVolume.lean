import WaringSiegel.WSL3PoissonMixedComplementS

/-! # Complementary mixed-sixth estimate with the last major moment exposed -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactMixedSComplementIntegral_volume_bound {u w g v : mixedSpace K → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (hus : ∀ x, u x ≠ 0 → ‖x‖ ≤ 1)
    (hun : ∀ x, u x = (‖u x‖:ℂ))
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : ∀ x, g x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H P M R : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P)
      (hM : 1 ≤ M) (hR : 1 ≤ R), H ≤ P → P ≤ H^2 →
      ‖compactMixedSComplementIntegral u w g v huc hwc hgc hvc H P M R
        (by linarith) (by linarith) (by linarith) (by linarith)‖^2 ≤
      C*(H^finrank ℚ K)*(P^finrank ℚ K : ℝ)^(1+ε)*(R^finrank ℚ K : ℝ)^(2+ε)*
        ((H^finrank ℚ K)*(M^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+ε) +
        (M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^(2+ε) +
        (M^finrank ℚ K)^2*(nonzeroCubicMajorFourth u huc H (by linarith))^((1:ℝ)/4)*
          (R^finrank ℚ K : ℝ)^((9:ℝ)/4+ε)) := by
  obtain ⟨Ci,hCi,hi⟩ := mixedComplementIntegral_volume_bound hw hwc hws hv hvc hvs hε
  obtain ⟨C0,C1,C2,hC0,hC1,hC2,hj⟩ := compactMixedJIntegral_volume_bound hu huc hus hg hgc hgs
    hv hvc hvs hε hε
  obtain ⟨W0,hW0⟩ := hu.continuous.bounded_above_of_compact_support huc
  let W := |W0|+1
  have hW : 0 < W := by dsimp [W]; positivity
  have hwU (x : mixedSpace K) : ‖u x‖ ≤ W :=
    (hW0 x).trans ((le_abs_self W0).trans (by dsimp [W]; linarith))
  let Cj := C0+C1+C2
  have hCj : 0 < Cj := by dsimp [Cj]; positivity
  refine ⟨W*Ci*Cj,by positivity,fun H P M R hH hP hM hR hHP hPH => ?_⟩
  have hH0 : 0 < H := by linarith
  have hP0 : 0 < P := by linarith
  have hM0 : 0 < M := by linarith
  have hR0 : 0 < R := by linarith
  let U := (compactIntegerSupport u huc H hH0.ne').erase 0
  have hU0 : ∀ h ∈ U, h ≠ 0 := fun h hh => (Finset.mem_erase.mp hh).1
  have hU : ∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H :=
    fun h hh => compactIntegerSupport_norm_bound huc hus H hH0 (Finset.mem_erase.mp hh).2
  have hI := hi P H R hP hR hH hHP hPH U hU0 hU
  have hS := compactMixedSComplementIntegral_cauchy u w g v huc hwc hgc hvc H P M R
    hH0 hP0 hM0.ne' hR0.ne' hun W hW.le hwU
  let A0 := (H^finrank ℚ K)*(M^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+ε)
  let A1 := (M^finrank ℚ K)^2*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^(2+ε)
  let A2 := (M^finrank ℚ K)^2*(nonzeroCubicMajorFourth u huc H hH0.ne')^((1:ℝ)/4)*
    (R^finrank ℚ K : ℝ)^((9:ℝ)/4+ε)
  have hMF := nonzeroCubicMajorFourth_nonneg u huc H hH0.ne'
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hA2 : 0 ≤ A2 := by dsimp [A2]; positivity
  have hJ : ‖compactMixedJIntegral u g v huc hgc hvc H M R hH0.ne' hM0.ne' hR0.ne'‖ ≤
      Cj*(A0+A1+A2) := by
    apply (hj H M R hH hM hR).trans
    calc
      _ = C0*A0+C1*A1+C2*A2 := by dsimp [A0,A1,A2]; ring
      _ ≤ Cj*A0+Cj*A1+Cj*A2 := by
        apply add_le_add
        · exact add_le_add (mul_le_mul_of_nonneg_right (by dsimp [Cj]; linarith) hA0)
            (mul_le_mul_of_nonneg_right (by dsimp [Cj]; linarith) hA1)
        · exact mul_le_mul_of_nonneg_right (by dsimp [Cj]; linarith) hA2
      _ = _ := by ring
  apply hS.trans
  calc
    _ ≤ (W*(Ci*H^finrank ℚ K*(P^finrank ℚ K : ℝ)^(1+ε)*(R^finrank ℚ K : ℝ)^(2+ε)))*
        (Cj*(A0+A1+A2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hI hW.le) hJ (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [A0,A1,A2]; ring

end WaringSiegel.WSL3Poisson
