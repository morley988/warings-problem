import Waring.RestrictedSmoothArcLabels
import Waring.RestrictedSmoothHolder

/-! # Exact integer dilation of the actual smooth moments -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Waring.RestrictedSmoothArcs
open SmoothMoments

theorem periodic_phase (k n : ℕ) : Function.Periodic (phase k n) 1 := by
  intro x
  rw [phase_eq_fourier,phase_eq_fourier,AddCircle.coe_add_period]

theorem periodic_smoothWeyl (k : ℕ) (P R : ℝ) :
    Function.Periodic (smoothWeyl k P R) 1 := by
  intro x
  unfold smoothWeyl
  exact Finset.sum_congr rfl (fun n _ => periodic_phase k n x)

theorem periodic_integral_integer_dilation {F : ℝ → ℝ} (hF : Continuous F)
    (hper : Function.Periodic F 1) (c : ℕ) (hc : 0 < c) :
    (∫ x in (0 : ℝ)..1, F ((c : ℝ)*x)) = ∫ x in (0 : ℝ)..1,F x := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hi := hper.intervalIntegral_add_zsmul_eq (c : ℤ) 0
    (fun a b => hF.intervalIntegrable a b)
  simp only [zsmul_eq_mul,Int.cast_natCast,mul_one,zero_add] at hi
  have hs := intervalIntegral.integral_comp_mul_left F (a := 0) (b := 1) hcR
  simpa only [mul_zero,mul_one,smul_eq_mul,hi,← mul_assoc,inv_mul_cancel₀ hcR,one_mul] using hs

theorem smoothMoment_integer_dilation (k s c : ℕ) (hc : 0 < c) (Y R : ℝ) :
    (∫ x in (0 : ℝ)..1, ‖smoothWeyl k Y R ((c : ℝ)*x)‖^s)=smoothMoment k s Y R := by
  exact periodic_integral_integer_dilation ((continuous_smoothWeyl k Y R).norm.pow s)
    (fun x => by rw [periodic_smoothWeyl k Y R x]) c hc

theorem sum_scaled_smooth_arc_integrals_le (A : Finset ArcLabel) {Q δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*Q*δ ≤ 1)
    (hQ : ∀ p ∈ A,(p.1 : ℝ) ≤ Q)
    (k s c : ℕ) (hc : 0 < c) (Y R : ℝ) :
    (∑ p ∈ A, arcLabelIntegral p (fun x => ‖smoothWeyl k Y R ((c : ℝ)*x)‖^s) δ) ≤
      3*smoothMoment k s Y R := by
  have hcont : Continuous (fun x : ℝ => ‖smoothWeyl k Y R ((c : ℝ)*x)‖^s) :=
    ((continuous_smoothWeyl k Y R).comp (continuous_const.mul continuous_id)).norm.pow s
  have hper : Function.Periodic (fun x : ℝ => ‖smoothWeyl k Y R ((c : ℝ)*x)‖^s) 1 := by
    intro x
    dsimp only
    rw [mul_add,mul_one]
    have h := (periodic_smoothWeyl k Y R).nat_mul c ((c : ℝ)*x)
    simpa only [mul_one] using congrArg (fun z : ℂ => ‖z‖^s) h
  have h := sum_arcLabelIntegral_le A hδ hδ1 hsmall hQ hcont hper (fun x => by positivity)
  rw [smoothMoment_integer_dilation k s c hc Y R] at h
  exact h

#print axioms smoothMoment_integer_dilation
#print axioms sum_scaled_smooth_arc_integrals_le
end Waring.RestrictedSmoothArcs
