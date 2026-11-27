import WaringSiegel.WSL4ArchComplexFamilies

/-! # Rapid complex linear tails uniformly over a compact amplitude family -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
set_option maxHeartbeats 1000000

theorem complex_cubic_normalized_gradient_gap {R : ℝ} (hR : 0 ≤ R)
    {t xi z : ℂ} (ht : ‖t‖ ≤ cubicTailRadius R)
    (hxi : ‖xi‖ = 1) (hz : ‖z‖ ≤ R) :
    (1:ℝ)/2 ≤ ‖3*t*z^2+xi‖ := by
  have hz2 : ‖z‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hn : ‖3*t*z^2‖ ≤ 1/2 := calc
    _ = 3*‖t‖*‖z‖^2 := by simp only [norm_mul,norm_pow]; norm_num
    _ ≤ 3*cubicTailRadius R*R^2 := mul_le_mul (by nlinarith) hz2 (sq_nonneg _)
      (mul_nonneg (by norm_num) (cubicTailRadius_pos R).le)
    _ ≤ 1/2 := cubicTailRadius_bound R
  have htri := norm_sub_le (3*t*z^2+xi) (3*t*z^2)
  have he : 3*t*z^2+xi-3*t*z^2 = xi := by ring
  rw [he,hxi] at htri
  linarith

/-- Arbitrary powers of linear-frequency decay, with one constant for all
amplitudes in the specified compact smooth family. -/
theorem complex_cubic_nonstationary_family {F : P × ℂ → ℂ} {R : ℝ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T) (hR : 0 ≤ R)
    (hFs : ∀ p, support (fun z => F (p,z)) ⊆ closedBall 0 R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ theta u : ℂ, 1 ≤ ‖u‖ →
      ‖theta‖ ≤ cubicTailRadius R * ‖u‖ →
      ‖u‖^n * ‖complexCubicOscillatoryIntegral (fun z => F (p,z)) theta u‖ ≤ C := by
  let G : (P × (ℂ × ℂ)) × ℂ → ℂ := fun q => F (q.1.1,q.2)
  let H : (P × (ℂ × ℂ)) × ℂ → ℂ := fun q => 3*q.1.2.1*q.2^2+q.1.2.2
  have hG : ContDiff ℝ ∞ G := hF.comp
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hH : ContDiff ℝ ∞ H := by fun_prop
  have hphi (q : P × (ℂ × ℂ)) :
      ContDiff ℝ ∞ (fun z : ℂ => 2*(q.2.1*z^3+q.2.2*z).re) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_id.pow 3)).add (contDiff_const.mul contDiff_id)))
  let U : Set (ℂ × ℂ) := closedBall 0 (cubicTailRadius R) ×ˢ sphere 0 1
  have hU : IsCompact U := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hgap : ∀ q ∈ T ×ˢ U, ∀ z ∈ tsupport (fun y => G (q,y)), (1:ℝ)/2 ≤ ‖H (q,z)‖ := by
    intro q hq z hz
    have ht : ‖q.2.1‖ ≤ cubicTailRadius R := by
      simpa only [mem_closedBall,dist_zero_right] using hq.2.1
    have hxi : ‖q.2.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hq.2.2
    have hs := (closure_minimal (hFs q.1) isClosed_closedBall) hz
    have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hs
    exact complex_cubic_normalized_gradient_gap hR ht hxi hz'
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound hG hH (hT.prod hU)
    (isCompact_closedBall 0 R) (fun q => hFs q.1)
    (phi := fun q z => 2*(q.2.1*z^3+q.2.2*z).re)
    (fun q _ => hphi q)
    (fun q _ z => complex_cubic_gradient_real q.2.1 q.2.2 z)
    (fun q _ z => complex_cubic_gradient_imag q.2.1 q.2.2 z)
    (by norm_num : (0:ℝ) < 1/2) hgap n
  refine ⟨C,hC,fun p hp theta u hu htheta => ?_⟩
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  have hu0 : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hu_pos.ne'
  have hn (z : ℂ) : ‖z/(‖u‖:ℂ)‖ = ‖z‖/‖u‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)]
  have hpar : (theta/(‖u‖:ℂ),u/(‖u‖:ℂ)) ∈ U := by
    constructor
    · simpa only [mem_closedBall, dist_zero_right, hn] using (div_le_iff₀ hu_pos).mpr htheta
    · simp only [mem_sphere, dist_zero_right, hn, div_self hu_pos.ne']
  have hi : complexCubicOscillatoryIntegral (fun z => F (p,z)) theta u =
      ∫ z, F (p,z) * scalarOscillatoryPhase ‖u‖
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
  simpa only [abs_of_nonneg (norm_nonneg u)] using hb (p,_) ⟨hp,hpar⟩ ‖u‖

#print axioms complex_cubic_nonstationary_family
end WaringSiegel.WSL4

