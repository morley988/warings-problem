import WaringSiegel.WSL3UnitRealCubicTail

/-!
# Uniform rapid tails at a complex place

The source direction is chosen from the normalized linear coefficient. Its
linear phase derivative is exactly one, and the cubic perturbation stays
smaller than one half. This gives arbitrary inverse powers uniformly in
both the angle and the magnitude of the linear coefficient.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

/-- Directional derivative of the actual complex trace phase. -/
theorem complex_cubic_fderiv (t xi z v : ℂ) :
    fderiv ℝ (fun y : ℂ => 2*(t*y^3+xi*y).re) z v =
      2*((3*t*z^2+xi)*v).re := by
  have hg := (((hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℂ) 3 (x := z)).const_mul t).add
    ((hasFDerivAt_id z).const_mul xi))
  have h := (Complex.reCLM.hasFDerivAt.comp z hg).const_mul (2:ℝ)
  change HasFDerivAt (fun y : ℂ => 2*(t*y^3+xi*y).re) _ z at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, Complex.reCLM_apply,
    smul_eq_mul]
  norm_num
  ring

theorem complex_cubic_normalized_fderiv (t xi z : ℂ) (hxi : ‖xi‖ = 1) :
    fderiv ℝ (fun y : ℂ => 2*(t*y^3+xi*y).re) z (conj xi/2) =
      1+(3*t*z^2*conj xi).re := by
  rw [complex_cubic_fderiv]
  have he : (3*t*z^2+xi)*(conj xi/2) = (3*t*z^2*conj xi+xi*conj xi)/2 := by ring
  rw [he, Complex.div_ofNat_re, Complex.add_re, Complex.mul_conj', hxi]
  norm_num
  ring

theorem complex_cubic_derivative_pos {R : ℝ} {t xi z : ℂ} (hR : 0 ≤ R)
    (ht : ‖t‖ ≤ cubicTailRadius R) (hxi : ‖xi‖ = 1) (hz : ‖z‖ ≤ R) :
    1/2 ≤ 1+(3*t*z^2*conj xi).re := by
  have hz2 : ‖z‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hb : |(3*t*z^2*conj xi).re| ≤ 1/2 := calc
    _ ≤ ‖3*t*z^2*conj xi‖ := Complex.abs_re_le_norm _
    _ = 3*‖t‖*‖z‖^2 := by simp only [norm_mul, norm_pow, Complex.norm_conj, hxi, mul_one]; norm_num
    _ ≤ 3*cubicTailRadius R*R^2 := mul_le_mul (by nlinarith) hz2 (sq_nonneg _)
      (mul_nonneg (by norm_num) (cubicTailRadius_pos R).le)
    _ ≤ 1/2 := cubicTailRadius_bound R
  linarith [neg_abs_le (3*t*z^2*conj xi).re]

/-- Literal complex-place trace integral, with trace(z) = 2 Re(z). -/
def complexCubicOscillatoryIntegral (f : ℂ → ℂ) (theta u : ℂ) : ℂ :=
  ∫ z : ℂ, f z * Complex.exp (Complex.I * (2*(theta*z^3+u*z).re : ℝ))

/-- Uniform rapid nonstationary decay for a general fixed complex-place
amplitude, including uniformity in the linear coefficient's direction. -/
theorem complex_cubic_nonstationary_bound {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ, 1 ≤ ‖u‖ →
      ‖theta‖ ≤ cubicTailRadius R * ‖u‖ →
      ‖u‖^n * ‖complexCubicOscillatoryIntegral f theta u‖ ≤ C := by
  let A : (ℂ × ℂ) × ℂ → ℂ := fun p =>
    (smoothPositiveReciprocal (1+(3*p.1.1*p.2^2*conj p.1.2).re) : ℝ)
  let v : ℂ × ℂ → ℂ := fun p => conj p.2/2
  have hpol : ContDiff ℝ ∞ (fun p : (ℂ × ℂ) × ℂ => 3*p.1.1*p.2^2*conj p.1.2) :=
    ((contDiff_const.mul (contDiff_fst.comp contDiff_fst)).mul (contDiff_snd.pow 2)).mul
      (Complex.conjCLE.contDiff.comp (contDiff_snd.comp contDiff_fst))
  have hA : ContDiff ℝ ∞ A := Complex.ofRealCLM.contDiff.comp
    (smoothPositiveReciprocal_contDiff.comp (contDiff_const.add (Complex.reCLM.contDiff.comp hpol)))
  have hv : ContDiff ℝ ∞ v := (Complex.conjCLE.contDiff.comp contDiff_snd).div_const 2
  have hphi (p : ℂ × ℂ) : ContDiff ℝ ∞ (fun z : ℂ => 2*(p.1*z^3+p.2*z).re) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_id.pow 3)).add (contDiff_const.mul contDiff_id)))
  let T : Set (ℂ × ℂ) := closedBall 0 (cubicTailRadius R) ×ˢ sphere 0 1
  have hT : IsCompact T := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hr (p : ℂ × ℂ) (hp : p ∈ T) (z : ℂ) (hz : z ∈ closedBall 0 R) :
      A (p,z) * (fderiv ℝ (fun y : ℂ => 2*(p.1*y^3+p.2*y).re) z (v p) : ℂ) = 1 := by
    have ht : ‖p.1‖ ≤ cubicTailRadius R := by simpa only [mem_closedBall, dist_zero_right] using hp.1
    have hxi : ‖p.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.2
    have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
    dsimp only [A, v]
    rw [complex_cubic_normalized_fderiv _ _ _ hxi]
    exact_mod_cast smoothPositiveReciprocal_mul (complex_cubic_derivative_pos hR ht hxi hz')
  obtain ⟨C,hC,hb⟩ := uniform_nonstationary_integral_bound hA hv hf hT
    (isCompact_closedBall 0 R) hfs (fun p _ => hphi p) hr n
  refine ⟨C,hC,fun theta u hu htheta => ?_⟩
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  have hu0 : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hu_pos.ne'
  have hn (z : ℂ) : ‖z/(‖u‖:ℂ)‖ = ‖z‖/‖u‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)]
  have hp : (theta/(‖u‖:ℂ),u/(‖u‖:ℂ)) ∈ T := by
    constructor
    · simpa only [mem_closedBall, dist_zero_right, hn] using (div_le_iff₀ hu_pos).mpr htheta
    · simp only [mem_sphere, dist_zero_right, hn, div_self hu_pos.ne']
  have hi : complexCubicOscillatoryIntegral f theta u =
      ∫ z, f z * scalarOscillatoryPhase ‖u‖
        (fun y : ℂ => 2*((theta/(‖u‖:ℂ))*y^3+(u/(‖u‖:ℂ))*y).re) z := by
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold scalarOscillatoryPhase
    congr 1
    have he : theta*z^3+u*z = (‖u‖:ℂ)*
        ((theta/(‖u‖:ℂ))*z^3+(u/(‖u‖:ℂ))*z) := by field_simp
    rw [he]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    push_cast
    ring
  rw [hi]
  simpa only [abs_of_nonneg (norm_nonneg u)] using hb _ hp ‖u‖

/-- The actual radial factor of the smooth product weight at a complex place. -/
def smoothComplexCubicIntegral (rho R : ℝ) (theta u : ℂ) : ℂ :=
  complexCubicOscillatoryIntegral
    (fun z => (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) : ℂ)) theta u

theorem smooth_complex_cubic_nonstationary_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ, 1 ≤ ‖u‖ →
      ‖theta‖ ≤ cubicTailRadius (2*R) * ‖u‖ →
      ‖u‖^n * ‖smoothComplexCubicIntegral rho R theta u‖ ≤ C := by
  apply complex_cubic_nonstationary_bound
    (Complex.ofRealCLM.contDiff.comp
      ((positiveSmoothWindow_contDiff (rho^2) (R^2)).comp complex_normSq_contDiff)) (by positivity)
  intro z hz
  have hz' : positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) ≠ 0 := by
    intro he
    apply hz
    change (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) : ℂ) = 0
    rw [he]
    rfl
  have hs := positiveSmoothWindow_support (sq_pos_of_pos hrho) (sq_pos_of_pos hR) hz'
  rw [Complex.normSq_eq_norm_sq] at hs
  simp only [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg z]

#print axioms complex_cubic_nonstationary_bound
#print axioms smooth_complex_cubic_nonstationary_bound
end WaringSiegel.WSL3
