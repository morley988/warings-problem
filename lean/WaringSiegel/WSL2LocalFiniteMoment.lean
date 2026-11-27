import WaringSiegel.WSL2LocalFiniteWeyl

/-!
# Exact finite-field cubic second moment

Character orthogonality identifies the second moment with the number of
pairs of equal cubes. A polynomial root count bounds each fiber by three.
-/

noncomputable section

open Polynomial
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel

variable {F : Type*} [Field F] [Fintype F]

theorem finite_field_cube_fiber_card (b : F) :
    (Finset.univ.filter (fun x : F => x ^ 3 = b)).card ≤ 3 := by
  let p : F[X] := X ^ 3 - C b
  have hp : p ≠ 0 := X_pow_sub_C_ne_zero (by decide) b
  have hs : Finset.univ.filter (fun x : F => x ^ 3 = b) ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    simpa only [p, Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using (Finset.mem_filter.mp hx).2
  exact (Finset.card_le_card hs).trans
    ((Multiset.toFinset_card_le _).trans (card_roots_X_pow_sub_C (by decide) b))

theorem finite_field_cubic_norm_sq_expansion (ψ : AddChar F ℂ) (a : F) :
    ((‖finiteFieldCubicSum ψ a‖ ^ 2 : ℝ) : ℂ) =
      ∑ x : F, ∑ y : F, ψ (a * (x ^ 3 - y ^ 3)) := by
  unfold finiteFieldCubicSum
  rw [WSL2.finite_sum_norm_sq_pair_expansion]
  trans ∑ x : F, ∑ y : F, ψ (a * x ^ 3) * conj (ψ (a * y ^ 3))
  · exact Finset.sum_product Finset.univ Finset.univ
      (fun p : F × F => ψ (a * p.1 ^ 3) * conj (ψ (a * p.2 ^ 3)))
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← finite_addChar_sub]
  congr 1
  ring

/-- Exact second moment, with literal cube-fiber cardinalities. -/
theorem finite_field_cubic_second_moment_eq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ‖finiteFieldCubicSum ψ a‖ ^ 2) =
      (Fintype.card F : ℝ) *
        ∑ x : F, ((Finset.univ.filter (fun y : F => y ^ 3 = x ^ 3)).card : ℝ) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp only [finite_field_cubic_norm_sq_expansion]
  rw [Finset.sum_comm]
  have hswap (x : F) : (∑ a : F, ∑ y : F, ψ (a * (x ^ 3 - y ^ 3))) =
      ∑ y : F, ∑ a : F, ψ (a * (x ^ 3 - y ^ 3)) := Finset.sum_comm
  simp only [hswap]
  simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have he (y : F) : (x ^ 3 = y ^ 3) ↔ (y ^ 3 = x ^ 3) := eq_comm
  simp only [he, apply_ite, Nat.cast_zero, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The total complete cubic second moment is at most `3q²`. -/
theorem finite_field_cubic_second_moment_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ‖finiteFieldCubicSum ψ a‖ ^ 2) ≤ 3 * (Fintype.card F : ℝ) ^ 2 := by
  rw [finite_field_cubic_second_moment_eq ψ hψ]
  calc
    (Fintype.card F : ℝ) *
        ∑ x : F, ((Finset.univ.filter (fun y : F => y ^ 3 = x ^ 3)).card : ℝ) ≤
      (Fintype.card F : ℝ) * ∑ _x : F, (3 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro x _
      have hb := finite_field_cube_fiber_card (F := F) (x ^ (3 : ℕ))
      exact_mod_cast hb
    _ = 3 * (Fintype.card F : ℝ) ^ 2 := by simp; ring

end WaringSiegel

#print axioms WaringSiegel.finite_field_cubic_second_moment_eq
#print axioms WaringSiegel.finite_field_cubic_second_moment_le
