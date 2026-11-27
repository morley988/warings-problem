import WaringSiegel.WSL4ArchLongThinDecay
import WaringSiegel.WSL3PoissonMixedKernelBounds
import WaringSiegel.WSL3PoissonMixedQuadraticBounds

/-! # Enlarged major bounds transported through actual Gaussian and linear Poisson -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3Poisson
open scoped BigOperators Classical NumberField ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem longThinOriginalGaussian_major_bound_enlarged
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (L : ℝ) (hL : 1 ≤ L)
    (γ : K) (hmaj : θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (L*P^finrank ℚ K) γ) :
    Summable (longThinOriginalGaussian θ P H) ∧
      (∑' p, longThinOriginalGaussian θ P H p) ≤
        (H^(finrank ℚ K) / ((4:ℝ)^nrComplexPlaces K * Real.pi^(finrank ℚ K))) *
          ((2*longThinGaussianFactor K*(longThinDualConstant (inverseDifferent K)*L^(5*finrank ℚ K)))*
            longThinMajorFactor (inverseDifferent K) θ P H γ) := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  refine ⟨(longThin_gaussian_summable θ P H hPp.ne' hHp.ne').2, ?_⟩
  rw [poisson_longThin_gaussian θ P H hPp.ne' hHp]
  exact mul_le_mul_of_nonneg_left
    (longThinMajorGaussian_summable_bound_enlarged _ inverseDifferent_ne_zero θ P H hP hH hPH L hL γ hmaj).2
    (by positivity)


theorem originalLongThinProductDecay_major_bound_enlarged (θ : mixedSpace K) (P H : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (L : ℝ) (hL : 1 ≤ L)
    (γ : K) (hmaj : θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (L*P^finrank ℚ K) γ) :
    Summable (fun p : originalLongThinDomain (K:=K) P H => originalLongThinProductDecay θ P p) ∧
      (∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p) ≤
        originalLongThinProductConstant K * L^(5*finrank ℚ K) * H^(finrank ℚ K) *
          longThinMajorFactor (inverseDifferent K) θ P H γ := by
  obtain ⟨hs, hb⟩ := originalLongThinProductDecay_summable_bound θ P H (by linarith) (by linarith)
  refine ⟨hs, hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_major_bound_enlarged θ P H hP hH hPH L hL γ hmaj).2
    (show 0 ≤ (2:ℝ)^(2*finrank ℚ K+2)*2*originalGaussianBoxFactor K by
      have hF := originalGaussianBoxFactor_pos (K:=K); positivity)
  convert h using 1
  · ring
  · unfold originalLongThinProductConstant originalThinMinorConstant
    ring

theorem compactQuadraticAverage_major_bound_enlarged {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → H ≤ P → P ≤ H^2 →
      ∀ θ : mixedSpace K, ∀ γ : K,
      (6*θ) ∈ productMajorArc (inverseDifferent K) (P^2*(2*H)) (L*P^finrank ℚ K) γ →
      ∀ α : 𝓞 K → mixedSpace K, ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2) ≤
        C*P^finrank ℚ K*H^finrank ℚ K*P^ε*
          longThinMajorFactor (inverseDifferent K) (6*θ) P (2*H) γ := by
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_bound_of_kernel hw hc hsupport hε
  have hLp : 0 < L := by linarith
  refine ⟨C*L^(5*finrank ℚ K),by positivity,fun P H hP hH hHP hPH θ γ hmaj α U hU0 hU => ?_⟩
  have hF := longThinMajorFactor_one_le (inverseDifferent K) inverseDifferent_ne_zero
    (6*θ) P (2*H) (by linarith) γ
  have hR : 1 ≤ L^(5*finrank ℚ K)*longThinMajorFactor (inverseDifferent K) (6*θ) P (2*H) γ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) hF
  have hk := (originalLongThinProductDecay_major_bound_enlarged (6*θ) P (2*H) hP
    (by linarith) (by nlinarith) L hL γ hmaj).2
  have hh := hb P H hP hH hHP θ _ hR
    (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hk) α U hU0 hU
  exact hh.trans_eq (by ring)

#print axioms originalLongThinProductDecay_major_bound_enlarged
#print axioms compactQuadraticAverage_major_bound_enlarged
end WaringSiegel.WSL4
