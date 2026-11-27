import WaringSiegel.WSL2LocalFiniteMoment

/-!
# Eighth-moment tail for complete cubic sums

Combining the fourth-power Weyl bound with the exact second moment gives a
summable-scale eighth-moment estimate. The squared bound avoids fractional
powers while retaining the sharp exponent needed for the Euler tail.
-/

noncomputable section

open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel

variable {F : Type*} [Field F] [Fintype F]

/-- The nontrivial-character eighth-power aggregate has square at most `72q¹³`. -/
theorem finite_field_cubic_eighth_sum_sq_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h6 : (6 : F) ≠ 0) :
    (∑ a ∈ (Finset.univ.erase (0 : F)), ‖finiteFieldCubicSum ψ a‖ ^ 8) ^ 2 ≤
      72 * (Fintype.card F : ℝ) ^ 13 := by
  let A : Finset F := Finset.univ.erase 0
  let t : F → ℝ := fun a => ‖finiteFieldCubicSum ψ a‖
  have h2 : (∑ a ∈ A, t a ^ 2) ≤ 3 * (Fintype.card F : ℝ) ^ 2 := by
    apply le_trans _ (finite_field_cubic_second_moment_le ψ hψ)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  have h14 (a : F) (ha : a ∈ A) : t a ^ 14 ≤
      8 * (Fintype.card F : ℝ) ^ 9 * t a ^ 2 := by
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hw := finite_field_cubic_weyl_fourth ψ hψ h6 ha0
    have hc := pow_le_pow_left₀ (by positivity : 0 ≤ t a ^ 4) hw 3
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (t a))
    convert hm using 1 <;> dsimp [t] <;> ring
  have h14sum : (∑ a ∈ A, t a ^ 14) ≤ 24 * (Fintype.card F : ℝ) ^ 11 := by
    calc
      (∑ a ∈ A, t a ^ 14) ≤
          ∑ a ∈ A, 8 * (Fintype.card F : ℝ) ^ 9 * t a ^ 2 :=
        Finset.sum_le_sum h14
      _ = 8 * (Fintype.card F : ℝ) ^ 9 * ∑ a ∈ A, t a ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 8 * (Fintype.card F : ℝ) ^ 9 * (3 * (Fintype.card F : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 24 * (Fintype.card F : ℝ) ^ 11 := by ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A t (fun a => t a ^ 7)
  have hp (a : F) : t a * t a ^ 7 = t a ^ 8 := by ring
  have hq (a : F) : (t a ^ 7) ^ 2 = t a ^ 14 := by ring
  simp only [hp, hq] at hc
  change (∑ a ∈ A, t a ^ 8) ^ 2 ≤ _
  calc
    (∑ a ∈ A, t a ^ 8) ^ 2 ≤ (∑ a ∈ A, t a ^ 2) * (∑ a ∈ A, t a ^ 14) := hc
    _ ≤ (3 * (Fintype.card F : ℝ) ^ 2) * (24 * (Fintype.card F : ℝ) ^ 11) :=
      mul_le_mul h2 h14sum (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = 72 * (Fintype.card F : ℝ) ^ 13 := by ring

end WaringSiegel

#print axioms WaringSiegel.finite_field_cubic_eighth_sum_sq_le
