import WaringSiegel.WSL2MomentDifferencing
import WaringSiegel.WSL2MomentHuaPolynomial

/-!
# Genuine pointwise cubic differencing

Two ordinary differences reduce a cubic phase to a linear phase. The
quartic Weyl inequality below is proved directly on the additive group of
the original ring, with the literal overlap domains and coefficient weights.
The lower polynomial coefficients disappear from the bound.
-/

noncomputable section
open Polynomial
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

section Additive
variable {G : Type*} [AddCommGroup G]

def shiftedWeight (w : G → ℂ) (h x : G) : ℂ := w (x+h) * conj (w x)

def doubleShiftedWeight (w : G → ℂ) (h j x : G) : ℂ :=
  shiftedWeight (shiftedWeight w h) j x

theorem finite_sum_norm_sq_le_correlations (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (f : G → ℂ) :
    ‖∑ x ∈ S, f x‖^2 ≤ ∑ h ∈ H, ‖∑ x ∈ additiveOverlap S h, shiftedWeight f h x‖ := by
  have h := congrArg norm (finite_sum_norm_sq_autocorrelations S H hH f)
  have hnorm : ‖((‖∑ x ∈ S, f x‖^2 : ℝ) : ℂ)‖ = ‖∑ x ∈ S, f x‖^2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hnorm] at h
  rw [h]
  exact norm_sum_le _ _

/-- The quartic Weyl differencing bound before estimating its linear sums. -/
theorem finite_sum_fourth_le_double_correlations (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (f : G → ℂ) :
    ‖∑ x ∈ S, f x‖^4 ≤ (H.card : ℝ) *
      ∑ h ∈ H, ∑ j ∈ H, ‖∑ x ∈ additiveOverlap (additiveOverlap S h) j,
        doubleShiftedWeight f h j x‖ := by
  have hfirst := finite_sum_fourth_le_correlations S H hH f
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro h hh
  exact finite_sum_norm_sq_le_correlations (additiveOverlap S h) H
    (fun x hx y hy => hH x (additiveOverlap_subset S h hx) y (additiveOverlap_subset S h hy))
    (shiftedWeight f h)

theorem doubleShiftedWeight_norm_le (S : Finset G) (w : G → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ x ∈ S, ‖w x‖ ≤ W)
    (h j x : G) (hx : x ∈ additiveOverlap (additiveOverlap S h) j) :
    ‖doubleShiftedWeight w h j x‖ ≤ W^4 := by
  obtain ⟨hxO, hxjO⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxS, hxhS⟩ := Finset.mem_filter.mp hxO
  obtain ⟨hxjS, hxjhS⟩ := Finset.mem_filter.mp hxjO
  dsimp [doubleShiftedWeight, shiftedWeight]
  rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have h₁ : ‖w (x+j+h)‖ * ‖w (x+j)‖ ≤ W*W :=
    mul_le_mul (hw _ hxjhS) (hw _ hxjS) (norm_nonneg _) hW
  have h₂ : ‖w (x+h)‖ * ‖w x‖ ≤ W*W :=
    mul_le_mul (hw _ hxhS) (hw _ hxS) (norm_nonneg _) hW
  have hprod := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  convert hprod using 1 <;> ring

end Additive

section Polynomial
variable {R ι : Type*} [CommRing R] [Fintype ι]

theorem norm_latticeCharacter_eq_one (m : ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    ‖latticeCharacter m θ‖ = 1 := by
  simp only [latticeCharacter, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

def finitePolynomialSum (S : Finset R) (coord : R →+ (ι → ℤ)) (p : R[X]) (w : R → ℂ)
    (θ : ι → AddCircle (1 : ℝ)) : ℂ :=
  ∑ x ∈ S, w x * latticeCharacter (coord (p.eval x)) θ

theorem polynomial_phase_correlation (coord : R →+ (ι → ℤ)) (p : R[X]) (w : R → ℂ)
    (h x : R) (θ : ι → AddCircle (1 : ℝ)) :
    shiftedWeight (fun x => w x * latticeCharacter (coord (p.eval x)) θ) h x =
      shiftedWeight w h x * latticeCharacter (coord ((polynomialDifference h p).eval x)) θ := by
  simp only [shiftedWeight, polynomialDifference_eval, map_sub, latticeCharacter_sub, map_mul]
  ring

/-- Literal polynomial phase version of the quartic differencing bound. -/
theorem polynomial_fourth_le_double_linear_sums (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (coord : R →+ (ι → ℤ))
    (p : R[X]) (w : R → ℂ) (θ : ι → AddCircle (1 : ℝ)) :
    ‖finitePolynomialSum S coord p w θ‖^4 ≤ (H.card : ℝ) *
      ∑ h ∈ H, ∑ j ∈ H, ‖finitePolynomialSum (additiveOverlap (additiveOverlap S h) j)
        coord (polynomialDifference j (polynomialDifference h p)) (doubleShiftedWeight w h j) θ‖ := by
  have h := finite_sum_fourth_le_double_correlations S H hH
    (fun x => w x * latticeCharacter (coord (p.eval x)) θ)
  have hphase (h : R) :
      shiftedWeight (fun x => w x * latticeCharacter (coord (p.eval x)) θ) h =
        (fun x => shiftedWeight w h x * latticeCharacter (coord ((polynomialDifference h p).eval x)) θ) :=
    funext (fun x => polynomial_phase_correlation coord p w h x θ)
  simpa only [finitePolynomialSum, doubleShiftedWeight, hphase, polynomial_phase_correlation] using h

def cubicPolynomial (a b c d : R) : R[X] := C a * X^3 + C b * X^2 + C c * X + C d

theorem cubicPolynomial_doubleDifference_eval (a b c d h j x : R) :
    (polynomialDifference j (polynomialDifference h (cubicPolynomial a b c d))).eval x =
      6*a*h*j*x + (3*a*h*j*(h+j) + 2*b*h*j) := by
  rw [double_polynomialDifference_eval]
  simp only [cubicPolynomial, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- Adding a phase constant does not affect the norm of a finite weighted sum. -/
theorem norm_linear_phase_add_constant (S : Finset R) (coord : R →+ (ι → ℤ))
    (a c : R) (w : R → ℂ) (θ : ι → AddCircle (1 : ℝ)) :
    ‖∑ x ∈ S, w x * latticeCharacter (coord (a*x+c)) θ‖ =
      ‖∑ x ∈ S, w x * latticeCharacter (coord (a*x)) θ‖ := by
  simp only [map_add, WaringSiegel.latticeCharacter_add, ← mul_assoc]
  rw [← Finset.sum_mul, norm_mul, norm_latticeCharacter_eq_one, mul_one]

/-- Actual cubic quartic Weyl inequality, uniform in all lower coefficients. -/
theorem cubic_fourth_le_linear_sums (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (coord : R →+ (ι → ℤ))
    (a b c d : R) (w : R → ℂ) (θ : ι → AddCircle (1 : ℝ)) :
    ‖finitePolynomialSum S coord (cubicPolynomial a b c d) w θ‖^4 ≤
      (H.card : ℝ) * ∑ h ∈ H, ∑ j ∈ H,
        ‖∑ x ∈ additiveOverlap (additiveOverlap S h) j,
          doubleShiftedWeight w h j x * latticeCharacter (coord (6*a*h*j*x)) θ‖ := by
  have h := polynomial_fourth_le_double_linear_sums S H hH coord (cubicPolynomial a b c d) w θ
  simpa only [finitePolynomialSum, cubicPolynomial_doubleDifference_eval,
    norm_linear_phase_add_constant] using h

end Polynomial
end WaringSiegel.WSL2
