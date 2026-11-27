import WaringSiegel.WSL3UnitRealStationary
import WaringSiegel.WSL3UnitCubicPruning

/-!
# Stationary square-root decay for the actual smooth real-place weight

Partial integration transfers the genuine interval estimate to the fixed
smooth window. The resulting constant is independent of the linear twist.
Both signs of the cubic coefficient and the bounded-frequency region are
included before restoring the literal 2π Fourier convention.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL3
set_option maxHeartbeats 800000

/-- Partial summation for a smooth amplitude whose upper endpoint vanishes. -/
theorem weighted_interval_bound_of_primitive {a b D M : ℝ} (hab : a ≤ b) (hD : 0 ≤ D)
    {w f : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (hf : Continuous f) (hwb : w b = 0)
    (hderiv : ∀ x ∈ Set.Icc a b, ‖deriv w x‖ ≤ D)
    (hprimitive : ∀ x ∈ Set.Icc a b, ‖∫ t in a..x, f t‖ ≤ M) :
    ‖∫ x in a..b, w x*f x‖ ≤ D*M*(b-a) := by
  let F : ℝ → ℂ := fun x => ∫ t in a..x, f t
  have hFc : Continuous F := intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) a
  have hFd (x : ℝ) : HasDerivAt F (f x) x := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable a x) hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hwc' : Continuous (deriv w) := hw.continuous_deriv (by simp)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := w) (u' := deriv w) (v := F) (v' := f)
    hw.continuous.continuousOn hFc.continuousOn
    (fun x _ => (hw.differentiable (by simp) x).hasDerivAt) (fun x _ => hFd x)
    (hwc'.intervalIntegrable a b) (hf.intervalIntegrable a b)
  have hFa : F a = 0 := by simp [F]
  rw [hwb, hFa, zero_mul, mul_zero, sub_self, zero_sub] at hi
  rw [hi, norm_neg]
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := D*M) (fun x hx => show ‖deriv w x*F x‖ ≤ D*M from by
      have hx' : x ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at hx
        exact Set.Ioc_subset_Icc_self hx
      rw [norm_mul]
      exact mul_le_mul (hderiv x hx') (hprimitive x hx') (norm_nonneg _) hD)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hm

theorem realCubicPhase_neg (theta u x : ℝ) :
    realCubicPhase (-theta) (-u) x = conj (realCubicPhase theta u x) := by
  rw [realCubicPhase, realCubicPhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem smoothRealCubicIntegral_neg (rho R theta u : ℝ) :
    smoothRealCubicIntegral rho R (-theta) (-u) = conj (smoothRealCubicIntegral rho R theta u) := by
  unfold smoothRealCubicIntegral realCubicOscillatoryIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  change (positiveSmoothWindow rho R x : ℂ)*realCubicPhase (-theta) (-u) x = _
  rw [realCubicPhase_neg, map_mul, Complex.conj_ofReal]
  rfl

theorem smoothRealCubicIntegral_eq_interval (rho R theta u : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (hab : rho/2 ≤ 2*R) :
    smoothRealCubicIntegral rho R theta u =
      ∫ x in rho/2..2*R, (positiveSmoothWindow rho R x : ℂ)*realCubicPhase theta u x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
  have hw : positiveSmoothWindow rho R x = 0 := by
    by_contra hn
    have hs := positiveSmoothWindow_support hrho hR hn
    exact hx ⟨hs.1.le,hs.2.le⟩
  simp only [hw, Complex.ofReal_zero, zero_mul]

/-- Actual square-root decay away from zero, initially for positive cubic
coefficient. The cutoff parameters and constant are fixed before θ and u. -/
theorem smoothRealCubicIntegral_positive_stationary (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ, 0 < theta →
      Real.sqrt theta * ‖smoothRealCubicIntegral rho R theta u‖ ≤ C := by
  by_cases hab : rho/2 ≤ 2*R
  · let w : ℝ → ℂ := fun x => (positiveSmoothWindow rho R x : ℂ)
    have hw : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp (positiveSmoothWindow_contDiff rho R)
    obtain ⟨D,hD,hbound⟩ := ((isCompact_Icc : IsCompact (Set.Icc (rho/2) (2*R))).image
      (hw.continuous_deriv (by simp))).isBounded.exists_pos_norm_le
    have hd (x : ℝ) (hx : x ∈ Set.Icc (rho/2) (2*R)) : ‖deriv w x‖ ≤ D :=
      hbound _ (Set.mem_image_of_mem _ hx)
    have hwb : w (2*R) = 0 := by
      dsimp only [w, positiveSmoothWindow]
      have he : 2-(2*R)/R = 0 := by field_simp; ring
      rw [he, Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, Complex.ofReal_zero]
    let C : ℝ := 9*D*(2*R-rho/2)/Real.sqrt (rho/2)+1
    have hba : 0 ≤ 2*R-rho/2 := sub_nonneg.mpr hab
    refine ⟨C, by dsimp only [C]; positivity, fun theta u ht => ?_⟩
    have hprimitive (x : ℝ) (hx : x ∈ Set.Icc (rho/2) (2*R)) :
        ‖∫ t in rho/2..x, realCubicPhase theta u t‖ ≤ 9/Real.sqrt (theta*(rho/2)) :=
      real_cubic_stationary_interval_bound (by positivity) hx.1 ht u
    have hi := weighted_interval_bound_of_primitive hab hD.le hw
      (realCubicPhase_contDiff theta u).continuous hwb hd hprimitive
    rw [← smoothRealCubicIntegral_eq_interval rho R theta u hrho hR hab] at hi
    have hscaled := mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg theta)
    have hs0 : Real.sqrt theta ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    have ha0 : Real.sqrt (rho/2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have he : Real.sqrt theta*(D*(9/Real.sqrt (theta*(rho/2)))*(2*R-rho/2)) =
        9*D*(2*R-rho/2)/Real.sqrt (rho/2) := by
      rw [Real.sqrt_mul ht.le]
      field_simp
    rw [he] at hscaled
    exact hscaled.trans (by dsimp only [C]; linarith)
  · refine ⟨1,zero_lt_one,fun theta u _ => ?_⟩
    have hz : smoothRealCubicIntegral rho R theta u = 0 := by
      unfold smoothRealCubicIntegral realCubicOscillatoryIntegral
      apply integral_eq_zero_of_ae
      filter_upwards [] with x
      have hw : positiveSmoothWindow rho R x = 0 := by
        by_contra hn
        have hs := positiveSmoothWindow_support hrho hR hn
        exact hab (hs.1.le.trans hs.2.le)
      simp only [hw, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
    simp [hz]

/-- Both signs of θ are covered by exact conjugation of the real weight. -/
theorem smoothRealCubicIntegral_abs_stationary (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      Real.sqrt |theta| * ‖smoothRealCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothRealCubicIntegral_positive_stationary rho R hrho hR
  refine ⟨C,hC,fun theta u => ?_⟩
  rcases lt_trichotomy theta 0 with ht | he | ht
  · have h := hb (-theta) (-u) (neg_pos.mpr ht)
    rw [smoothRealCubicIntegral_neg, Complex.norm_conj] at h
    simpa only [abs_of_neg ht] using h
  · simp [he,hC.le]
  · simpa only [abs_of_pos ht] using hb theta u ht

/-- Literal 2π Fourier phase, with the bounded-frequency region included. -/
theorem realPlaceCubicIntegral_stationary_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      Real.sqrt (1+|theta|) * ‖realPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothRealCubicIntegral_abs_stationary rho R hrho hR
  let M : ℝ := volume.real (closedBall (0:ℝ) (2*R))
  have hM : 0 ≤ M := measureReal_nonneg
  refine ⟨2*C+2*M+1,by positivity,fun theta u => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  by_cases ht : 1 ≤ |theta|
  · have habs : |theta| ≤ |2*Real.pi*theta| := by
      rw [abs_mul (2*Real.pi) theta, abs_of_pos hp]
      nlinarith [abs_nonneg theta]
    have hs : Real.sqrt (1+|theta|) ≤ 2*Real.sqrt |2*Real.pi*theta| := by
      calc
        _ ≤ Real.sqrt (4*|2*Real.pi*theta|) := Real.sqrt_le_sqrt (by linarith)
        _ = _ := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
          have h4 : Real.sqrt (4:ℝ) = 2 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
          rw [h4]
    have hb' := hb (2*Real.pi*theta) (2*Real.pi*u)
    rw [← realPlaceCubicIntegral_eq_rescaled] at hb'
    have hm := mul_le_mul_of_nonneg_right hs (norm_nonneg (realPlaceCubicIntegral rho R theta u))
    nlinarith
  · have hs : Real.sqrt (1+|theta|) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> linarith [abs_nonneg theta, le_of_not_ge ht]
    have hb' := realPlaceCubicIntegral_norm_le rho R theta u hrho hR
    have hm := mul_le_mul hs hb' (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
    change Real.sqrt (1+|theta|)*‖realPlaceCubicIntegral rho R theta u‖ ≤ 2*M at hm
    linarith

#print axioms smoothRealCubicIntegral_abs_stationary
#print axioms realPlaceCubicIntegral_stationary_bound
end WaringSiegel.WSL3
