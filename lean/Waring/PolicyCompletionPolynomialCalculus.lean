import Waring.PolicyCompletionPolynomialDiscrete
import Waring.EndgameCompletionSingular
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Actual oscillatory integrals of positive-coefficient polynomial phases

Integration by parts uses the reciprocal of the first derivative. The
second derivative is nonnegative, so its entire error integral telescopes.
This proves an upper-endpoint-independent tail bound for the literal
polynomial phase, uniformly in every coefficient.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialCalculus
open Polynomial QuadraticModulation EndgameCompletion PolicyCompletionPolynomialDiscrete

def polynomialIntegral (f : Polynomial ℝ) (P β : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..P, e (β*f.eval t)

theorem hasDerivAt_polynomial_e (f : Polynomial ℝ) (β t : ℝ) :
    HasDerivAt (fun x : ℝ => e (β*f.eval x))
      (e (β*f.eval t) * (((2*Real.pi*β*f.derivative.eval t : ℝ) : ℂ)*Complex.I)) t := by
  have h := (((f.hasDerivAt t).const_mul (2*Real.pi*β)).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1
  · funext x
    unfold e
    congr 1
    push_cast
    ring
  · unfold e
    congr 1
    · congr 1
      push_cast
      ring

theorem deriv_polynomial_e (f : Polynomial ℝ) (β t : ℝ) :
    deriv (fun x : ℝ => e (β*f.eval x)) t =
      e (β*f.eval t) * (((2*Real.pi*β*f.derivative.eval t : ℝ) : ℂ)*Complex.I) :=
  (hasDerivAt_polynomial_e f β t).deriv

theorem continuous_polynomial_e (f : Polynomial ℝ) (β : ℝ) :
    Continuous (fun t : ℝ => e (β*f.eval t)) := by
  unfold e
  fun_prop

theorem continuous_deriv_polynomial_e (f : Polynomial ℝ) (β : ℝ) :
    Continuous (deriv (fun x : ℝ => e (β*f.eval x))) := by
  simp only [funext (deriv_polynomial_e f β)]
  unfold e
  fun_prop

theorem norm_deriv_polynomial_e_le (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) (β : ℝ) {P t : ℝ} (ht : t ∈ Set.Icc 0 P) :
    ‖deriv (fun x : ℝ => e (β*f.eval x)) t‖ ≤
      2*Real.pi*|β| *f.derivative.eval P := by
  rw [deriv_polynomial_e, norm_mul, norm_e, one_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (eval_nonneg f.derivative (derivative_nonnegative f hf) ht.1)]
  exact mul_le_mul_of_nonneg_left
    (eval_monotone f.derivative (derivative_nonnegative f hf) ht.1 ht.2) (by positivity)

theorem norm_polynomialIntegral_le (f : Polynomial ℝ) {P : ℝ}
    (hP : 0 ≤ P) (β : ℝ) : ‖polynomialIntegral f P β‖ ≤ P := by
  simpa only [polynomialIntegral, sub_zero, abs_of_nonneg hP, one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
      (a := 0) (b := P) (fun t _ => (norm_e (β*f.eval t)).le)

theorem norm_polynomial_integral_tail_le (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) {A P β : ℝ}
    (hA : 0 ≤ A) (hAP : A ≤ P) (hβ : β ≠ 0) (hfirst : 0 < f.derivative.eval A) :
    ‖∫ t in A..P, e (β*f.eval t)‖ ≤ 1/(Real.pi*|β| *f.derivative.eval A) := by
  let g : ℝ → ℝ := fun t => (f.derivative.eval t)⁻¹
  let g' : ℝ → ℝ := fun t => -(f.derivative.derivative.eval t)/(f.derivative.eval t)^2
  let C : ℂ := (((2*Real.pi*β : ℝ) : ℂ)*Complex.I)⁻¹
  have hd := derivative_nonnegative f hf
  have hpos : ∀ t ∈ Set.Icc A P, 0 < f.derivative.eval t := fun t ht =>
    hfirst.trans_le (eval_monotone f.derivative hd hA ht.1)
  have hgc : ContinuousOn g (Set.Icc A P) :=
    f.derivative.continuous.continuousOn.inv₀ (fun t ht => (hpos t ht).ne')
  have hg'c : ContinuousOn g' (Set.Icc A P) :=
    f.derivative.derivative.continuous.continuousOn.neg.div
      (f.derivative.continuous.continuousOn.pow 2) (fun t ht => pow_ne_zero _ (hpos t ht).ne')
  have hgd : ∀ t ∈ Set.Icc A P, HasDerivAt g (g' t) t := by
    intro t ht
    exact (f.derivative.hasDerivAt t).inv (hpos t ht).ne'
  have hgneg : ∀ t ∈ Set.Icc A P, g' t ≤ 0 := by
    intro t ht
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (eval_nonneg f.derivative.derivative (derivative_nonnegative _ hd)
        (hA.trans ht.1))) (sq_nonneg _)
  have hident : ∀ t ∈ Set.Icc A P,
      C*(g t : ℂ)*deriv (fun x : ℝ => e (β*f.eval x)) t = e (β*f.eval t) := by
    intro t ht
    rw [deriv_polynomial_e]
    dsimp [C, g]
    have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
    have hfc : ((f.derivative.eval t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos t ht).ne'
    have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hβc, hfc, hπc, Complex.I_ne_zero]
  have hmain := norm_integral_le_two_mul_of_reciprocal_deriv hAP C
    (continuous_polynomial_e f β).continuousOn (continuous_deriv_polynomial_e f β).continuousOn
    hgc hg'c (fun t _ => (hasDerivAt_polynomial_e f β t).differentiableAt.hasDerivAt)
    hgd hident (fun t _ => (norm_e _).le)
    (inv_nonneg.mpr hfirst.le) (inv_nonneg.mpr (hpos P ⟨hAP,le_rfl⟩).le) hgneg
  have hCnorm : ‖C‖ = (2*Real.pi*|β|)⁻¹ := by
    dsimp [C]
    simp only [norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg Real.pi_pos.le]
  apply hmain.trans_eq
  rw [hCnorm]
  dsimp [g]
  field_simp [Real.pi_ne_zero, abs_ne_zero.mpr hβ, hfirst.ne']

theorem derivative_eval_lower (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    {d : ℕ} {H x : ℝ} (hd : 1 ≤ d) (hH : 0 < H) (hcoeff : H ≤ f.coeff d)
    (hx : 0 ≤ x) : H*(d : ℝ)*x^(d-1) ≤ f.derivative.eval x := by
  have hdmem : d ∈ f.support := Polynomial.mem_support_iff.mpr (hH.trans_le hcoeff).ne'
  rw [Polynomial.derivative_eval, Polynomial.sum]
  calc
    _ ≤ f.coeff d*(d : ℝ)*x^(d-1) := by gcongr
    _ ≤ _ := Finset.single_le_sum (f := fun i : ℕ => f.coeff i*(i:ℝ)*x^(i-1)) (fun i _ =>
      mul_nonneg (mul_nonneg (hf i) (Nat.cast_nonneg _)) (pow_nonneg hx _)) hdmem

#print axioms norm_polynomial_integral_tail_le
#print axioms derivative_eval_lower
end Waring.PolicyCompletionPolynomialCalculus
