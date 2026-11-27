import WaringSiegel.WSL3UnitGradientNonstationary
import WaringSiegel.WSL3UnitComplexCubicTail

/-!
# Genuine complex-plane cancellation from a nonvanishing complex derivative

The two real directional derivatives are combined using a globally smooth
regularized reciprocal of the squared complex derivative. The derivative
gap is required only on the actual parameter-dependent source support.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL3
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
set_option maxHeartbeats 1000000

/-- Arbitrary powers for an actual complex oscillatory integral whose real
phase is twice the real part of a complex differentiable phase. -/
theorem uniform_complex_gradient_integral_bound
    {F H : P × ℂ → ℂ} {phi : P → ℂ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    {T : Set P} {S : Set ℂ} (hT : IsCompact T) (hS : IsCompact S)
    (hFs : ∀ p, support (fun z => F (p,z)) ⊆ S)
    (hphi : ∀ p ∈ T, ContDiff ℝ ∞ (phi p))
    (hreal : ∀ p ∈ T, ∀ z, fderiv ℝ (phi p) z 1 = 2*(H (p,z)).re)
    (himag : ∀ p ∈ T, ∀ z, fderiv ℝ (phi p) z Complex.I = -2*(H (p,z)).im)
    {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ p ∈ T, ∀ z ∈ tsupport (fun y => F (p,y)), delta ≤ ‖H (p,z)‖)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ lambda : ℝ,
      |lambda|^n * ‖∫ z : ℂ, F (p,z)*scalarOscillatoryPhase lambda (phi p) z‖ ≤ C := by
  let q : P × ℂ → ℝ := fun p => Complex.normSq (H p)/delta^2
  let A : P × ℂ → ℂ := fun p => ((H p).re/(2*delta^2)*smoothPositiveReciprocal (q p) : ℝ)
  let B : P × ℂ → ℂ := fun p => (-(H p).im/(2*delta^2)*smoothPositiveReciprocal (q p) : ℝ)
  have hq : ContDiff ℝ ∞ q := (complex_normSq_contDiff.comp hH).div_const _
  have hA : ContDiff ℝ ∞ A := Complex.ofRealCLM.contDiff.comp
    (((Complex.reCLM.contDiff.comp hH).div_const _).mul (smoothPositiveReciprocal_contDiff.comp hq))
  have hB : ContDiff ℝ ∞ B := Complex.ofRealCLM.contDiff.comp
    (((Complex.imCLM.contDiff.comp hH).neg.div_const _).mul (smoothPositiveReciprocal_contDiff.comp hq))
  apply uniform_gradient_nonstationary_integral_bound hA hB
    (v := fun _ => (1:ℂ)) (w := fun _ => Complex.I) contDiff_const contDiff_const hF hT hS hFs hphi
  intro p hp z hz
  dsimp only [A,B]
  rw [hreal p hp z,himag p hp z]
  have hsq : delta^2 ≤ ‖H (p,z)‖^2 := pow_le_pow_left₀ hdelta.le (hgap p hp z hz) 2
  have hqpos : 1/2 ≤ q (p,z) := by
    dsimp only [q]
    rw [Complex.normSq_eq_norm_sq]
    apply (le_div_iff₀ (sq_pos_of_pos hdelta)).mpr
    nlinarith
  have hr := smoothPositiveReciprocal_mul hqpos
  have he : ((H (p,z)).re/(2*delta^2)*smoothPositiveReciprocal (q (p,z)))*(2*(H (p,z)).re) +
      (-(H (p,z)).im/(2*delta^2)*smoothPositiveReciprocal (q (p,z)))*(-2*(H (p,z)).im) = 1 := by
    calc
      _ = smoothPositiveReciprocal (q (p,z)) *
          (((H (p,z)).re^2+(H (p,z)).im^2)/delta^2) := by field_simp
      _ = smoothPositiveReciprocal (q (p,z))*q (p,z) := by
        dsimp only [q]
        rw [Complex.normSq_apply]
        ring
      _ = 1 := hr
  exact_mod_cast he

/-- The two actual real directional derivatives of the complex cubic trace phase. -/
theorem complex_cubic_gradient_real (theta u z : ℂ) :
    fderiv ℝ (fun y : ℂ => 2*(theta*y^3+u*y).re) z 1 =
      2*(3*theta*z^2+u).re := by
  rw [complex_cubic_fderiv,mul_one]

theorem complex_cubic_gradient_imag (theta u z : ℂ) :
    fderiv ℝ (fun y : ℂ => 2*(theta*y^3+u*y).re) z Complex.I =
      -2*(3*theta*z^2+u).im := by
  rw [complex_cubic_fderiv]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
  ring

#print axioms uniform_complex_gradient_integral_bound
end WaringSiegel.WSL3
