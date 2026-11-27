import Waring.SeedCompletionFirstWeyl

/-! # Integer ordinary-difference identity at arbitrary previous depth -/

noncomputable section
namespace Waring.SeedCompletionFamilyWeyl
open IntegerDifferencePolynomial SeedCompletionBackward SeedCompletionBackwardMoments

/-- The new coefficient is exactly one; all old heights are doubled. -/
theorem integer_backward_identity (k : ℕ) (params : List (ℤ×ℤ))
    (hm : ∀ p ∈ params,p.2 ≠ 0) (z z' : ℤ) :
    (powerPolynomial k ((z-z',1)::doubleHeights params)).eval (z+z') =
      (2 : ℤ)^k*((powerPolynomial k params).eval z-(powerPolynomial k params).eval z') := by
  have hmnew : ∀ p ∈ (z-z',1)::doubleHeights params,p.2 ≠ 0 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · norm_num
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact hm q hq
  apply (Int.cast_injective (α := ℝ))
  push_cast
  rw [powerPolynomial_eval_int k _ hmnew,
    powerPolynomial_eval_int k _ hm,powerPolynomial_eval_int k _ hm]
  have H := backward_phase_identity k (realParameters params) (z : ℝ) (z' : ℝ)
    ((z-z' : ℤ) : ℝ) 1 (by push_cast; simp)
  have hparams : realParameters ((z-z',1)::doubleHeights params) =
      (((z : ℝ)-(z' : ℝ)),1)::scaleHeights 2 (realParameters params) := by
    rw [show realParameters ((z-z',1)::doubleHeights params) =
      (((z-z' : ℤ) : ℝ),1)::realParameters (doubleHeights params) by
        simp only [realParameters,List.map_cons,Int.cast_one],
      realParameters_doubleHeights]
    simp only [Int.cast_sub]
  rw [hparams]
  simpa only [Int.cast_add,Int.cast_sub,one_pow,div_one] using H

#print axioms integer_backward_identity
end Waring.SeedCompletionFamilyWeyl
