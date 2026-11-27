import WaringSiegel.WSL2LocalFiniteEighth

/-!
# Finite-field eight-cube counts and an elementary Euler-tail estimate

Fourier orthogonality connects the complete cubic sums to literal tuple
counts. The squared normalized error is at most `72/q³`, equivalent to an
error of order `q^(-3/2)` and sufficient for an Euler-product tail.
-/

noncomputable section

open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel

variable {F : Type*} [Field F] [Fintype F]

def finiteFieldCubicSolutionCount (F : Type*) [Field F] (s : ℕ) (b : F) : ℕ :=
  Nat.card {x : Fin s → F // (∑ i, x i ^ 3) = b}

theorem finite_addChar_sum {ι : Type*} (ψ : AddChar F ℂ) (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ψ.map_add_eq_mul, ih]

theorem finite_field_cubic_power_expansion
    (ψ : AddChar F ℂ) (s : ℕ) (a b : F) :
    finiteFieldCubicSum ψ a ^ s * ψ (-a * b) =
      ∑ x : Fin s → F, ψ (a * ((∑ i, x i ^ 3) - b)) := by
  rw [finiteFieldCubicSum, Fintype.sum_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  have hp : (∏ i, ψ (a * x i ^ 3)) = ψ (a * ∑ i, x i ^ 3) := by
    rw [Finset.mul_sum, finite_addChar_sum]
  rw [hp, ← ψ.map_add_eq_mul]
  congr 1
  ring

/-- Exact orthogonality identity for the actual finite-field tuple count. -/
theorem finite_field_cubic_fourier_count
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (s : ℕ) (b : F) :
    (∑ a : F, finiteFieldCubicSum ψ a ^ s * ψ (-a * b)) =
      (Fintype.card F : ℂ) * (finiteFieldCubicSolutionCount F s b : ℂ) := by
  simp only [finite_field_cubic_power_expansion]
  rw [Finset.sum_comm]
  simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero, apply_ite, Nat.cast_zero,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold finiteFieldCubicSolutionCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

@[simp] theorem finite_field_cubic_sum_zero (ψ : AddChar F ℂ) :
    finiteFieldCubicSum ψ 0 = Fintype.card F := by
  simp [finiteFieldCubicSum]

/-- Removing the trivial frequency leaves precisely the representation-count error. -/
theorem finite_field_cubic_fourier_tail
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (s : ℕ) (b : F) :
    (∑ a ∈ (Finset.univ.erase (0 : F)), finiteFieldCubicSum ψ a ^ s * ψ (-a * b)) =
      (Fintype.card F : ℂ) * (finiteFieldCubicSolutionCount F s b : ℂ) -
        (Fintype.card F : ℂ) ^ s := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
    finite_field_cubic_fourier_count ψ hψ]
  simp only [finite_field_cubic_sum_zero, neg_zero, zero_mul, ψ.map_zero_eq_one, mul_one]

theorem finite_field_cubic_eight_error_norm_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (b : F) :
    ‖(Fintype.card F : ℂ) * (finiteFieldCubicSolutionCount F 8 b : ℂ) -
      (Fintype.card F : ℂ) ^ 8‖ ≤
        ∑ a ∈ (Finset.univ.erase (0 : F)), ‖finiteFieldCubicSum ψ a‖ ^ 8 := by
  rw [← finite_field_cubic_fourier_tail ψ hψ 8 b]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro a _
  simp only [norm_mul, norm_pow, finite_addChar_norm_one, mul_one, le_refl]

/-- Squared error at the unnormalized Fourier scale. -/
theorem finite_field_cubic_eight_error_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h6 : (6 : F) ≠ 0) (b : F) :
    ((Fintype.card F : ℝ) * (finiteFieldCubicSolutionCount F 8 b : ℝ) -
      (Fintype.card F : ℝ) ^ 8) ^ 2 ≤ 72 * (Fintype.card F : ℝ) ^ 13 := by
  have hnorm := finite_field_cubic_eight_error_norm_le ψ hψ b
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have h := hpow.trans (finite_field_cubic_eighth_sum_sq_le ψ hψ h6)
  have he : (Fintype.card F : ℂ) * (finiteFieldCubicSolutionCount F 8 b : ℂ) -
      (Fintype.card F : ℂ) ^ 8 =
      (((Fintype.card F : ℝ) * (finiteFieldCubicSolutionCount F 8 b : ℝ) -
        (Fintype.card F : ℝ) ^ 8 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- Elementary normalized eight-cube error: its square is at most `72/q³`.
This is an explicit `O(q^(-3/2))` error, proved without a Weil bound. -/
theorem finite_field_eight_cubes_normalized_error_sq
    (h6 : (6 : F) ≠ 0) (b : F) :
    ((finiteFieldCubicSolutionCount F 8 b : ℝ) / (Fintype.card F : ℝ) ^ 7 - 1) ^ 2 ≤
      72 / (Fintype.card F : ℝ) ^ 3 := by
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have h := finite_field_cubic_eight_error_sq ψ hψ h6 b
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card F : ℝ) * (finiteFieldCubicSolutionCount F 8 b : ℝ) -
      (Fintype.card F : ℝ) ^ 8 =
      (Fintype.card F : ℝ) ^ 8 *
        ((finiteFieldCubicSolutionCount F 8 b : ℝ) / (Fintype.card F : ℝ) ^ 7 - 1) := by
    field_simp
  rw [he, mul_pow] at h
  apply (le_div_iff₀ (pow_pos hq 3)).mpr
  apply (mul_le_mul_left (pow_pos hq 13)).mp
  convert h using 1 <;> ring

theorem finite_field_eight_cubes_normalized_error_abs
    (h6 : (6 : F) ≠ 0) (b : F) :
    |(finiteFieldCubicSolutionCount F 8 b : ℝ) / (Fintype.card F : ℝ) ^ 7 - 1| ≤
      Real.sqrt (72 / (Fintype.card F : ℝ) ^ 3) := by
  have h := Real.sqrt_le_sqrt (finite_field_eight_cubes_normalized_error_sq h6 b)
  simpa only [Real.sqrt_sq_eq_abs] using h

end WaringSiegel

#print axioms WaringSiegel.finite_field_cubic_fourier_count
#print axioms WaringSiegel.finite_field_cubic_eight_error_norm_le

#print axioms WaringSiegel.finite_field_eight_cubes_normalized_error_sq
