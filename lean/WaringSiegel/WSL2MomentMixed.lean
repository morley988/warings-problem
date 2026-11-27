import WaringSiegel.WSL2MomentDifferencing

/-!
# Literal mixed moments and finite collision counts

This module expands the actual Haar integral used after one Cauchy step in
the eighth-moment argument. No orthogonality hypothesis is supplied.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2
variable {ι α β : Type*} [Fintype ι]

def finiteFrequencySum (S : Finset α) (v : α → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) : ℂ := ∑ x ∈ S, latticeCharacter (v x) θ

def fourthFrequency (v : α → ι → ℤ) (q : (α × α) × (α × α)) : ι → ℤ :=
  (v q.1.1 - v q.1.2) - (v q.2.1 - v q.2.2)

theorem finiteFrequencySum_norm_sq_expansion (S : Finset α) (v : α → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    ((‖finiteFrequencySum S v θ‖^2 : ℝ) : ℂ) =
      finiteFrequencySum (S.product S) (fun p => v p.1 - v p.2) θ := by
  rw [finiteFrequencySum, finite_sum_norm_sq_pair_expansion]
  exact Finset.sum_congr rfl (fun p _ => (latticeCharacter_sub _ _ θ).symm)

theorem finiteFrequencySum_norm_fourth_expansion (S : Finset α) (v : α → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    ((‖finiteFrequencySum S v θ‖^4 : ℝ) : ℂ) =
      finiteFrequencySum ((S.product S).product (S.product S)) (fourthFrequency v) θ := by
  have h := finiteFrequencySum_norm_sq_expansion (S.product S) (fun p => v p.1 - v p.2) θ
  rw [← finiteFrequencySum_norm_sq_expansion] at h
  have hn : ‖((‖finiteFrequencySum S v θ‖^2 : ℝ) : ℂ)‖^2 =
      ‖finiteFrequencySum S v θ‖^4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    ring
  simpa only [hn, fourthFrequency] using h

theorem finiteFrequencySum_mul (S : Finset α) (T : Finset β)
    (v : α → ι → ℤ) (u : β → ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    finiteFrequencySum S v θ * finiteFrequencySum T u θ =
      finiteFrequencySum (S.product T) (fun p => v p.1 + u p.2) θ := by
  unfold finiteFrequencySum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ a ∈ S, ∑ b ∈ T, latticeCharacter (v a) θ * latticeCharacter (u b) θ) =
        ∑ a ∈ S, ∑ b ∈ T, latticeCharacter (v a + u b) θ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_congr rfl (fun b _ => (WaringSiegel.latticeCharacter_add _ _ θ).symm)
    _ = _ := (Finset.sum_product S T (fun p => latticeCharacter (v p.1 + u p.2) θ)).symm

theorem integral_finiteFrequencySum (S : Finset α) (v : α → ι → ℤ) :
    (∫ θ, finiteFrequencySum S v θ ∂latticeHaar) =
      ((S.filter (fun x => v x = 0)).card : ℂ) := by
  have h := integral_weighted_lattice_sum S (fun _ => (1 : ℂ)) v 0
  simpa [finiteFrequencySum, Finset.sum_boole] using h

theorem integral_fourth_mul_second_count (S : Finset α) (T : Finset β)
    (v : α → ι → ℤ) (u : β → ι → ℤ) :
    (∫ θ, ‖finiteFrequencySum S v θ‖^4 * ‖finiteFrequencySum T u θ‖^2 ∂latticeHaar) =
      (((((S.product S).product (S.product S)).product (T.product T)).filter
        (fun q => fourthFrequency v q.1 = -(u q.2.1 - u q.2.2))).card : ℝ) := by
  have hexp (θ : ι → AddCircle (1 : ℝ)) :
      ((‖finiteFrequencySum S v θ‖^4 * ‖finiteFrequencySum T u θ‖^2 : ℝ) : ℂ) =
      finiteFrequencySum (((S.product S).product (S.product S)).product (T.product T))
        (fun q => fourthFrequency v q.1 + (u q.2.1 - u q.2.2)) θ := by
    rw [Complex.ofReal_mul, finiteFrequencySum_norm_fourth_expansion,
      finiteFrequencySum_norm_sq_expansion, finiteFrequencySum_mul]
  calc
    (∫ θ, ‖finiteFrequencySum S v θ‖^4 * ‖finiteFrequencySum T u θ‖^2 ∂latticeHaar) =
        (∫ θ, ((‖finiteFrequencySum S v θ‖^4 * ‖finiteFrequencySum T u θ‖^2 : ℝ) : ℂ)
          ∂latticeHaar).re := by rw [integral_complex_ofReal]; rfl
    _ = _ := by
      simp_rw [hexp]
      rw [integral_finiteFrequencySum]
      simp only [add_eq_zero_iff_eq_neg, Complex.natCast_re]

end WaringSiegel.WSL2
