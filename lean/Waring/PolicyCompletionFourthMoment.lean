import Waring.UnseparatedDifferencing
import Waring.GeometricSums

/-!
# An actual fourth-moment Weyl step

One unseparated ordinary difference preserves the original label. The
pointwise square bound, multiplied by the original squared norm, and
Young's inequality imply an integrated fourth-moment bound in terms of
the original second moment and the literal differenced second moment.
No arithmetic or source moment estimate is assumed.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Waring.PolicyCompletionFourthMoment
open UnseparatedDifferencing

theorem fourth_from_square_bound (X Y L N : ℝ)
    (h : X^2 ≤ N*L^2+2*L*Y) : X^4 ≤ 2*N*L^2*X^2+4*L^2*Y^2 := by
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg X)
  have hy := sq_nonneg (X^2-2*L*Y)
  nlinarith

/-- Pointwise Young absorption gives the fourth-moment step with constant
four in the differenced energy. -/
theorem integral_fourth_le_second_add_difference (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (L N : ℝ)
    (hpoint : ∀ α : ℝ, ‖F α‖^2 ≤ N*L^2+2*L*‖G α‖) :
    (∫ α in (0 : ℝ)..1, ‖F α‖^4) ≤
      2*N*L^2*(∫ α in (0 : ℝ)..1, ‖F α‖^2) +
        4*L^2*(∫ α in (0 : ℝ)..1, ‖G α‖^2) := by
  have hiF := (hF.norm.pow 2).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have hiG := (hG.norm.pow 2).intervalIntegrable (μ := volume) (0 : ℝ) 1
  calc
    _ ≤ ∫ α in (0 : ℝ)..1, 2*N*L^2*‖F α‖^2+4*L^2*‖G α‖^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one
        ((hF.norm.pow 4).intervalIntegrable (0 : ℝ) 1) ((hiF.const_mul _).add (hiG.const_mul _))
      intro α hα
      exact fourth_from_square_bound _ _ _ _ (hpoint α)
    _ = _ := by
      rw [intervalIntegral.integral_add (hiF.const_mul _) (hiG.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]

/-- The complete finite-family fourth moment, with the same labels in its
actual first difference and arbitrary continuous bounded phases. -/
theorem family_fourth_moment_bound {ι : Type*} (B : Finset ι)
    (domain : ι → Finset ℤ) (f : ℝ → ι → ℤ → ℂ) (N : ℕ)
    (hcontinuous : ∀ b z, Continuous (fun α : ℝ => f α b z))
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ α : ℝ, ∀ b ∈ B, ∀ z, ‖f α b z‖ ≤ 1) :
    (∫ α in (0 : ℝ)..1, ‖familySum B domain (f α)‖^4) ≤
      2*(N : ℝ)*(B.card : ℝ)^2*
        (∫ α in (0 : ℝ)..1, ‖familySum B domain (f α)‖^2) +
      4*(B.card : ℝ)^2*
        (∫ α in (0 : ℝ)..1, ‖firstDifference B domain (f α) N‖^2) := by
  have hF : Continuous (fun α : ℝ => familySum B domain (f α)) := by
    unfold familySum
    exact continuous_finset_sum B (fun b _ =>
      continuous_finset_sum (domain b) (fun z _ => hcontinuous b z))
  have hG : Continuous (fun α : ℝ => firstDifference B domain (f α) N) := by
    unfold firstDifference familySum
    apply continuous_finset_sum
    intro bu hbu
    apply continuous_finset_sum
    intro z hz
    exact (hcontinuous bu.1 (z+bu.2)).mul (Complex.continuous_conj.comp (hcontinuous bu.1 z))
  exact integral_fourth_le_second_add_difference _ _ hF hG (B.card : ℝ) N
    (fun α => first_unseparated_bound B domain (f α) N hcard hwidth (hnorm α))

/-- Integer polynomial frequencies automatically satisfy the continuity
and unit-norm hypotheses of the generic fourth-moment Weyl step. -/
theorem fourier_family_fourth_moment_bound {ι : Type*} (B : Finset ι)
    (domain : ι → Finset ℤ) (phase : ι → ℤ → ℤ) (N : ℕ)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ)) :
    (∫ α in (0 : ℝ)..1,
      ‖familySum B domain (fun b z => fourier (phase b z) (α : AddCircle (1 : ℝ)))‖^4) ≤
      2*(N : ℝ)*(B.card : ℝ)^2*
        (∫ α in (0 : ℝ)..1,
          ‖familySum B domain (fun b z => fourier (phase b z) (α : AddCircle (1 : ℝ)))‖^2) +
      4*(B.card : ℝ)^2*
        (∫ α in (0 : ℝ)..1,
          ‖firstDifference B domain
            (fun b z => fourier (phase b z) (α : AddCircle (1 : ℝ))) N‖^2) := by
  apply family_fourth_moment_bound
  · intro b z
    exact (fourier (phase b z)).continuous.comp (AddCircle.continuous_mk' 1)
  · exact hcard
  · exact hwidth
  · intro α b hb z
    exact le_of_eq (norm_fourier_value _ _)

#print axioms integral_fourth_le_second_add_difference
#print axioms family_fourth_moment_bound
#print axioms fourier_family_fourth_moment_bound
end Waring.PolicyCompletionFourthMoment
