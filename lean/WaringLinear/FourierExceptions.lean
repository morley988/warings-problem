import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Positivity

/-! # Power-saving exceptional sets from the scalar circle method

A target with zero representations has a minor-arc Fourier coefficient
cancelling the positive major-arc term. Bessel's inequality bounds the
number of such targets by the normalized minor-arc second moment.
-/

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate
namespace WaringLinear

/-- The finite exceptional-set inequality for actual Fourier coefficients
on the circle of mass one. -/
theorem fourier_exceptional_mass {T : ℝ} [hT : Fact (0<T)]
    (f : Lp ℂ 2 (@haarAddCircle T hT)) (E : Finset ℤ) (c : ℝ) (hc : 0 ≤ c)
    (hE : ∀ n ∈ E, c ≤ ‖fourierCoeff f n‖) :
    (E.card : ℝ) * c ^ 2 ≤ ∫ x : AddCircle T, ‖f x‖ ^ 2 ∂haarAddCircle := by
  have hB : (E.card : ℝ) * c ^ 2 ≤ ‖f‖ ^ 2 := by
    calc
      (E.card : ℝ) * c ^ 2 = ∑ _n ∈ E, c ^ 2 := by simp
      _ ≤ ∑ n ∈ E, ‖fourierCoeff f n‖ ^ 2 := by
        exact Finset.sum_le_sum (fun i hi => pow_le_pow_left₀ hc (hE i hi) 2)
      _ = ∑ n ∈ E, ‖inner ℂ (fourierBasis n) f‖ ^ 2 := by
        simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
      _ ≤ ‖f‖ ^ 2 := fourierBasis.orthonormal.sum_inner_products_le f
  have hh := congr_arg RCLike.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at hh
  · simp only [← norm_sq_eq_re_inner] at hh
    exact hB.trans_eq hh
  · exact L2.integrable_inner f f

/-- A uniform major-arc lower bound for a target set together with an
upper bound on the minor-arc second moment gives a cardinality bound.
The representation and major arc coefficients may be complex. -/
theorem unrepresented_le_fourier_energy {T : ℝ} [hT : Fact (0<T)]
    (f : Lp ℂ 2 (@haarAddCircle T hT)) (E : Finset ℤ)
    (R A : ℤ → ℂ) (c D : ℝ) (hc : 0<c)
    (hzero : ∀ n ∈ E, R n=0)
    (hdecomp : ∀ n ∈ E, R n=A n+fourierCoeff f n)
    (hmain : ∀ n ∈ E, c ≤ ‖A n‖)
    (hminor : (∫ x : AddCircle T, ‖f x‖^2 ∂haarAddCircle) ≤ D) :
    (E.card : ℝ) ≤ D/c^2 := by
  apply (le_div_iff₀ (pow_pos hc _)).2
  apply (fourier_exceptional_mass f E c hc.le ?_).trans hminor
  intro n hn
  have hn' := hdecomp n hn
  rw [hzero n hn] at hn'
  have hh : fourierCoeff f n = -A n :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hn'.symm)
  simpa only [hh,norm_neg] using hmain n hn

#print axioms fourier_exceptional_mass
#print axioms unrepresented_le_fourier_energy
end WaringLinear
