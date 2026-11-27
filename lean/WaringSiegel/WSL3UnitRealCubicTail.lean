import WaringSiegel.WSL3UnitNonstationaryCore
import WaringSiegel.WSL3UnitSmoothCutoff

/-!
# Uniform rapid tails for the real cubic phase with linear twist

A smooth global reciprocal agrees with the true reciprocal derivative on
all source points and normalized frequency parameters of interest. Repeated
integration by parts therefore gives arbitrary inverse powers uniformly in
the region where the linear coefficient dominates the cubic coefficient.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff
namespace WaringSiegel.WSL3
set_option maxHeartbeats 800000

/-- A globally smooth regularized reciprocal, equal to 1/t for t ≥ 1/2. -/
def smoothPositiveReciprocal (t : ℝ) : ℝ := Real.smoothTransition (4*t-1) / t

@[fun_prop] theorem smoothPositiveReciprocal_contDiff :
    ContDiff ℝ ∞ smoothPositiveReciprocal := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have he : ∀ᶠ y : ℝ in 𝓝 0, y < 1/4 := eventually_lt_nhds (by norm_num)
    filter_upwards [he] with y hy
    simp only [smoothPositiveReciprocal,
      Real.smoothTransition.zero_of_nonpos (by linarith : 4*y-1 ≤ 0), zero_div]
  · exact (Real.smoothTransition.contDiffAt.comp x
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)).div contDiffAt_id hx

theorem smoothPositiveReciprocal_mul {t : ℝ} (ht : 1/2 ≤ t) :
    smoothPositiveReciprocal t * t = 1 := by
  have hn : t ≠ 0 := by linarith
  rw [smoothPositiveReciprocal, Real.smoothTransition.one_of_one_le (by linarith),
    div_mul_cancel₀ 1 hn]

/-- Explicit compact normalized-frequency radius for source radius R. -/
def cubicTailRadius (R : ℝ) : ℝ := (6*(1+R^2))⁻¹

theorem cubicTailRadius_pos (R : ℝ) : 0 < cubicTailRadius R := by
  unfold cubicTailRadius
  positivity

theorem cubicTailRadius_bound (R : ℝ) : 3*cubicTailRadius R*R^2 ≤ 1/2 := by
  have hR : 0 < 6*(1+R^2) := by positivity
  unfold cubicTailRadius
  calc
    _ = (3*R^2)/(6*(1+R^2)) := by ring
    _ ≤ 1/2 := (div_le_iff₀ hR).mpr (by nlinarith)

/-- The directional derivative is uniformly separated from zero on the
compact source and normalized-frequency sets. -/
theorem real_cubic_derivative_pos {R t x : ℝ} (hR : 0 ≤ R)
    (ht : |t| ≤ cubicTailRadius R) (hx : |x| ≤ R) :
    1/2 ≤ 1+3*t*x^2 := by
  have hx2 : x^2 ≤ R^2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hb : |3*t*x^2| ≤ 1/2 := calc
    |3*t*x^2| = 3 * |t| * x^2 := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ)≤3), abs_of_nonneg (sq_nonneg x)]
    _ ≤ 3*cubicTailRadius R*R^2 :=
      mul_le_mul (by nlinarith) hx2 (sq_nonneg x)
        (mul_nonneg (by norm_num) (cubicTailRadius_pos R).le)
    _ ≤ 1/2 := cubicTailRadius_bound R
  linarith [neg_abs_le (3*t*x^2)]

theorem real_cubic_fderiv (t x : ℝ) :
    fderiv ℝ (fun y : ℝ => y+t*y^3) x 1 = 1+3*t*x^2 := by
  rw [fderiv_deriv]
  have h := ((hasDerivAt_id x).add ((hasDerivAt_pow 3 x).const_mul t)).deriv
  convert h using 1 <;> norm_num <;> ring

/-- A literal real cubic-plus-linear oscillatory integral. -/
def realCubicOscillatoryIntegral (f : ℝ → ℂ) (theta u : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (Complex.I * (theta*x^3+u*x : ℝ))

/-- Quantitative nonstationary decay, uniform over the full linear-dominant
region. The source amplitude is any fixed smooth function supported in the
specified compact interval. -/
theorem real_cubic_nonstationary_bound {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      |theta| ≤ cubicTailRadius R * |u| →
      |u|^n * ‖realCubicOscillatoryIntegral f theta u‖ ≤ C := by
  let A : ℝ × ℝ → ℂ := fun p => (smoothPositiveReciprocal (1+3*p.1*p.2^2) : ℝ)
  have hA : ContDiff ℝ ∞ A := by
    exact Complex.ofRealCLM.contDiff.comp (smoothPositiveReciprocal_contDiff.comp (by fun_prop))
  have hphi (t : ℝ) : ContDiff ℝ ∞ (fun x : ℝ => x+t*x^3) := by fun_prop
  have hr (t : ℝ) (ht : t ∈ closedBall 0 (cubicTailRadius R))
      (x : ℝ) (hx : x ∈ closedBall 0 R) :
      A (t,x) * (fderiv ℝ (fun y : ℝ => y+t*y^3) x (1:ℝ) : ℂ) = 1 := by
    have ht' : |t| ≤ cubicTailRadius R := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht
    have hx' : |x| ≤ R := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hx
    rw [real_cubic_fderiv]
    dsimp only [A]
    exact_mod_cast smoothPositiveReciprocal_mul (real_cubic_derivative_pos hR ht' hx')
  obtain ⟨C,hC,hb⟩ := uniform_nonstationary_integral_bound hA
    (v := fun _ : ℝ => (1:ℝ)) contDiff_const hf
    (isCompact_closedBall 0 (cubicTailRadius R)) (isCompact_closedBall 0 R) hfs
    (fun t _ => hphi t) hr n
  refine ⟨C,hC,fun theta u hu => ?_⟩
  have ht : theta/u ∈ closedBall 0 (cubicTailRadius R) := by
    simp only [mem_closedBall, Real.dist_eq, sub_zero, abs_div]
    by_cases hz : u = 0
    · simp [hz, (cubicTailRadius_pos R).le]
    · exact (div_le_iff₀ (abs_pos.mpr hz)).mpr hu
  have htheta : theta/u*u = theta := by
    by_cases hz : u = 0
    · have : theta = 0 := by simpa [hz] using hu
      simp [hz, this]
    · exact div_mul_cancel₀ theta hz
  have hi : realCubicOscillatoryIntegral f theta u =
      ∫ x, f x * scalarOscillatoryPhase u (fun y : ℝ => y+(theta/u)*y^3) x := by
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    unfold scalarOscillatoryPhase
    congr 1
    have he : theta*x^3+u*x = u*(x+(theta/u)*x^3) := by
      calc
        _ = (theta/u*u)*x^3+u*x := by rw [htheta]
        _ = _ := by ring
    rw [he]
    push_cast
    ring
  rw [hi]
  exact hb (theta/u) ht u

/-- The explicit real place factor used by the smooth product weight. -/
def smoothRealCubicIntegral (rho R theta u : ℝ) : ℂ :=
  realCubicOscillatoryIntegral (fun x => (positiveSmoothWindow rho R x : ℂ)) theta u

theorem smooth_real_cubic_nonstationary_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      |theta| ≤ cubicTailRadius (2*R) * |u| →
      |u|^n * ‖smoothRealCubicIntegral rho R theta u‖ ≤ C := by
  apply real_cubic_nonstationary_bound
    (Complex.ofRealCLM.contDiff.comp (positiveSmoothWindow_contDiff rho R)) (by positivity)
  intro x hx
  have hx' : positiveSmoothWindow rho R x ≠ 0 := by
    intro hz
    apply hx
    change (positiveSmoothWindow rho R x : ℂ) = 0
    rw [hz]
    rfl
  have hs := positiveSmoothWindow_support hrho hR hx'
  simp only [mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < x)]
  exact hs.2.le

#print axioms real_cubic_nonstationary_bound
#print axioms smooth_real_cubic_nonstationary_bound
end WaringSiegel.WSL3
