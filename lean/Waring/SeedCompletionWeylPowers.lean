import Waring.PolicyCompletionFourthMoment

/-! # Moment doubling for the literal unseparated difference

The elementary split at `X² ≤ 2A` keeps a lower moment of the original
family in the diagonal term. In particular, the eighth-moment step has
the required fourth-moment diagonal, with no extra parameter count.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Waring.SeedCompletionWeylPowers
open UnseparatedDifferencing

theorem double_even_from_square_bound (X Y A B : ℝ) (r : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (h : X^2 ≤ A+B*Y) :
    X^(4*r) ≤ (2*A)^r*X^(2*r)+(2*B)^(2*r)*Y^(2*r) := by
  have hX : 0 ≤ X^(2*r) := by rw [pow_mul]; positivity
  by_cases hc : X^2 ≤ 2*A
  · have hp := pow_le_pow_left₀ (sq_nonneg X) hc r
    have hm := mul_le_mul_of_nonneg_right hp hX
    have he : X^(4*r) = (X^2)^r*X^(2*r) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [he]
    exact hm.trans (le_add_of_nonneg_right (by positivity))
  · have hc' : X^2 ≤ 2*B*Y := by linarith
    have hp := pow_le_pow_left₀ (sq_nonneg X) hc' (2*r)
    have he : (X^2)^(2*r) = X^(4*r) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [he,mul_pow] at hp
    exact hp.trans (le_add_of_nonneg_left (by positivity))

theorem integral_double_even_le (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (A B : ℝ) (r : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpoint : ∀ α : ℝ, ‖F α‖^2 ≤ A+B*‖G α‖) :
    (∫ α in (0 : ℝ)..1, ‖F α‖^(4*r)) ≤
      (2*A)^r*(∫ α in (0 : ℝ)..1, ‖F α‖^(2*r))+
      (2*B)^(2*r)*(∫ α in (0 : ℝ)..1, ‖G α‖^(2*r)) := by
  have hiF := (hF.norm.pow (2*r)).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have hiG := (hG.norm.pow (2*r)).intervalIntegrable (μ := volume) (0 : ℝ) 1
  calc
    _ ≤ ∫ α in (0 : ℝ)..1,
        (2*A)^r*‖F α‖^(2*r)+(2*B)^(2*r)*‖G α‖^(2*r) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        ((hF.norm.pow (4*r)).intervalIntegrable (0 : ℝ) 1)
        ((hiF.const_mul _).add (hiG.const_mul _))
      intro α hα
      exact double_even_from_square_bound _ _ _ _ r hA hB (norm_nonneg _) (hpoint α)
    _ = _ := by
      rw [intervalIntegral.integral_add (hiF.const_mul _) (hiG.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]

theorem family_double_even_moment_bound {ι : Type*} (B : Finset ι)
    (domain : ι → Finset ℤ) (f : ℝ → ι → ℤ → ℂ) (N r : ℕ)
    (hcontinuous : ∀ b z, Continuous (fun α : ℝ => f α b z))
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ α : ℝ, ∀ b ∈ B, ∀ z, ‖f α b z‖ ≤ 1) :
    (∫ α in (0 : ℝ)..1, ‖familySum B domain (f α)‖^(4*r)) ≤
      (2*(N : ℝ)*(B.card : ℝ)^2)^r*
        (∫ α in (0 : ℝ)..1, ‖familySum B domain (f α)‖^(2*r))+
      (4*(B.card : ℝ))^(2*r)*
        (∫ α in (0 : ℝ)..1, ‖firstDifference B domain (f α) N‖^(2*r)) := by
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
  have H := integral_double_even_le _ _ hF hG
    ((N : ℝ)*(B.card : ℝ)^2) (2*(B.card : ℝ)) r (by positivity) (by positivity)
    (fun α => first_unseparated_bound B domain (f α) N hcard hwidth (hnorm α))
  simpa only [show (2 : ℝ)*((N : ℝ)*(B.card : ℝ)^2) =
      2*(N : ℝ)*(B.card : ℝ)^2 by ring,
    show (2 : ℝ)*(2*(B.card : ℝ)) = 4*(B.card : ℝ) by ring] using H

theorem fourier_family_double_even_moment_bound {ι : Type*} (B : Finset ι)
    (domain : ι → Finset ℤ) (phase : ι → ℤ → ℤ) (N r : ℕ)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ)) :
    (∫ α in (0 : ℝ)..1,
      ‖familySum B domain (fun b z => fourier (phase b z) (α : AddCircle (1 : ℝ)))‖^(4*r)) ≤
      (2*(N : ℝ)*(B.card : ℝ)^2)^r*
        (∫ α in (0 : ℝ)..1,
          ‖familySum B domain (fun b z => fourier (phase b z) (α : AddCircle (1 : ℝ)))‖^(2*r))+
      (4*(B.card : ℝ))^(2*r)*
        (∫ α in (0 : ℝ)..1,
          ‖firstDifference B domain
            (fun b z => fourier (phase b z) (α : AddCircle (1 : ℝ))) N‖^(2*r)) := by
  apply family_double_even_moment_bound
  · intro b z
    exact (fourier (phase b z)).continuous.comp (AddCircle.continuous_mk' 1)
  · exact hcard
  · exact hwidth
  · intro α b hb z
    exact le_of_eq (norm_fourier_value _ _)

#print axioms integral_double_even_le
#print axioms fourier_family_double_even_moment_bound
end Waring.SeedCompletionWeylPowers
