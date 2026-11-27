import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # A shortening step for real-order moments

The weighted children contribute X^2 times
sum_m m^(p−1)(X/m)^(p+D), where p=r−2−k and D is the old excess.
The lower bound m≥X^θ contracts that excess to (1−θ)D.
-/

namespace WaringLinear
open scoped BigOperators

theorem shorten_child_excess {ι : Type*} [Fintype ι] (m : ι → ℝ)
    (X p D θ : ℝ) (hX : 0<X) (hD : 0≤D)
    (hm : ∀ i, 0<m i) (hsize : ∀ i, X^θ≤m i)
    (hmass : (∑ i, (m i)⁻¹)≤1) :
    (∑ i, (m i)^(p-1)*(X/m i)^(p+D)) ≤ X^(p+(1-θ)*D) := by
  have hXθ : X^(1-θ)*X^θ=X := by rw [←Real.rpow_add hX]; simp
  have hchild (i) : (X/m i)^D ≤ X^((1-θ)*D) := by
    rw [Real.rpow_mul hX.le]
    apply Real.rpow_le_rpow (div_nonneg hX.le (hm i).le) _ hD
    apply (div_le_iff₀ (hm i)).2
    calc
      X = X^(1-θ)*X^θ := hXθ.symm
      _ ≤ X^(1-θ)*m i := mul_le_mul_of_nonneg_left (hsize i) (Real.rpow_nonneg hX.le _)
  have hid i : (m i)^(p-1)*(X/m i)^(p+D) = X^p*((m i)⁻¹*(X/m i)^D) := by
    rw [Real.rpow_sub (hm i),Real.rpow_one,Real.rpow_add (div_pos hX (hm i)),
      Real.div_rpow hX.le (hm i).le]
    field_simp [(hm i).ne', (Real.rpow_pos_of_pos (hm i) p).ne']
  calc
    _ = ∑ i, X^p*((m i)⁻¹*(X/m i)^D) := Finset.sum_congr rfl (fun i _ => hid i)
    _ ≤ ∑ i, X^p*((m i)⁻¹*X^((1-θ)*D)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hchild i) (inv_nonneg.mpr (hm i).le)) (Real.rpow_nonneg hX.le _)
    _ = X^p*((∑ i, (m i)⁻¹)*X^((1-θ)*D)) := by rw [Finset.sum_mul,Finset.mul_sum]
    _ ≤ X^p*(1*X^((1-θ)*D)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hX.le _)) (Real.rpow_nonneg hX.le _)
    _ = _ := by rw [one_mul,←Real.rpow_add hX]

/-- The low spectrum inequality at two real moment orders. -/
theorem small_spectrum_pointwise (x X r h z : ℝ) (hx : 0≤x) (hX : 0<X)
    (hh : 0<h) (hr : h<r) (hsmall : x≤X^(1-z)) :
    x^r ≤ X^((1-z)*(r-h))*x^h := by
  by_cases hzero : x=0
  · simp [hzero,Real.zero_rpow hh.ne',Real.zero_rpow (ne_of_gt (lt_trans hh hr))]
  have hxpos := lt_of_le_of_ne hx (Ne.symm hzero)
  have hdiff := Real.rpow_le_rpow hx hsmall (sub_nonneg.mpr hr.le)
  rw [← Real.rpow_mul hX.le] at hdiff
  have h := mul_le_mul_of_nonneg_right hdiff (Real.rpow_nonneg hx h)
  rwa [←Real.rpow_add hxpos,sub_add_cancel] at h

#print axioms shorten_child_excess
#print axioms small_spectrum_pointwise
end WaringLinear
