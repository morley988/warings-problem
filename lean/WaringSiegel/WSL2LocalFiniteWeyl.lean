import WaringSiegel.WSL2MomentCubicWeyl
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Elementary finite-field cubic Weyl bounds

Two additive differences reduce the complete cubic sum to linear character
sums. Orthogonality then gives a fourth-power bound without a Weil estimate.
-/

noncomputable section

open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel

variable {F : Type*} [Field F] [Fintype F]

def finiteFieldCubicSum (ψ : AddChar F ℂ) (a : F) : ℂ := ∑ x : F, ψ (a * x ^ 3)

theorem finite_addChar_norm_one (ψ : AddChar F ℂ) (x : F) : ‖ψ x‖ = 1 := by
  have hchar : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  simpa only [IsUnit.unit_spec] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.val_mem_rootsOfUnity x hchar)

theorem finite_addChar_sub (ψ : AddChar F ℂ) (x y : F) :
    ψ (x - y) = ψ x * conj (ψ y) := by
  rw [ψ.map_sub_eq_div, div_eq_mul_inv, Complex.inv_eq_conj (finite_addChar_norm_one ψ y)]

theorem finite_addChar_shiftedWeight (ψ : AddChar F ℂ) (f : F → F) (h x : F) :
    WSL2.shiftedWeight (fun t => ψ (f t)) h x = ψ (f (x + h) - f x) := by
  exact (finite_addChar_sub ψ _ _).symm

theorem finite_addChar_double_cubic (ψ : AddChar F ℂ) (a h j x : F) :
    WSL2.doubleShiftedWeight (fun t => ψ (a * t ^ 3)) h j x =
      ψ (6 * a * h * j * x + 3 * a * h * j * (h + j)) := by
  have hh : WSL2.shiftedWeight (fun t => ψ (a * t ^ 3)) h =
      fun t => ψ (a * (t + h) ^ 3 - a * t ^ 3) :=
    funext (fun t => finite_addChar_shiftedWeight ψ _ h t)
  rw [WSL2.doubleShiftedWeight, hh, finite_addChar_shiftedWeight]
  congr 1
  ring

theorem finite_addChar_linear_sum_norm (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (b c : F) :
    ‖∑ x : F, ψ (b * x + c)‖ = if b = 0 then (Fintype.card F : ℝ) else 0 := by
  classical
  have he : (∑ x : F, ψ (b * x + c)) = (∑ x : F, ψ (x * b)) * ψ c := by
    simp only [ψ.map_add_eq_mul, Finset.sum_mul, mul_comm b]
  rw [he, norm_mul, finite_addChar_norm_one, mul_one, AddChar.sum_mulShift b hψ]
  split_ifs <;> simp

/-- The complete cubic Weyl bound `|S(a)|^4 ≤ 2q^3` for `6a ≠ 0`. -/
theorem finite_field_cubic_weyl_fourth
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h6 : (6 : F) ≠ 0)
    {a : F} (ha : a ≠ 0) :
    ‖finiteFieldCubicSum ψ a‖ ^ 4 ≤ 2 * (Fintype.card F : ℝ) ^ 3 := by
  classical
  have h := WSL2.finite_sum_fourth_le_double_correlations
    (Finset.univ : Finset F) Finset.univ (by simp) (fun x => ψ (a * x ^ 3))
  simp only [WSL2.additiveOverlap, Finset.mem_univ, Finset.filter_true,
    Finset.card_univ, finite_addChar_double_cubic,
    finite_addChar_linear_sum_norm ψ hψ] at h
  apply h.trans
  have hq : 0 ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  calc
    (Fintype.card F : ℝ) * ∑ h : F, ∑ j : F,
        (if 6 * a * h * j = 0 then (Fintype.card F : ℝ) else 0) ≤
      (Fintype.card F : ℝ) * ∑ h : F, ∑ j : F,
        ((if h = 0 then (Fintype.card F : ℝ) else 0) +
          (if j = 0 then (Fintype.card F : ℝ) else 0)) := by
      apply mul_le_mul_of_nonneg_left _ hq
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro j _
      by_cases hh : h = 0 <;> by_cases hj : j = 0 <;>
        simp [hh, hj, h6, ha, hq]
    _ = 2 * (Fintype.card F : ℝ) ^ 3 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum]
      ring

end WaringSiegel

#print axioms WaringSiegel.finite_field_cubic_weyl_fourth
