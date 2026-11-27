import WaringSiegel.WSL3CubicSquareRoot
import WaringSiegel.WSL2LocalFourUnit

/-! # WSL3: sharp-scale finite-field cubic counts and the cutoff 173 -/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace WaringSiegel
variable {F : Type*} [Field F] [Fintype F]

theorem finite_field_unit_cubic_norm_le_three_sqrt
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) {a : F} (ha : a ≠ 0) :
    ‖finiteFieldUnitCubicSum ψ a‖ ≤ 3 * Real.sqrt (Fintype.card F : ℝ) := by
  have h := finite_field_unit_cubic_norm_le ψ a
  have hc := finite_field_cubic_sum_norm_le_two_sqrt ψ hψ ha
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : 1 ≤ Real.sqrt (Fintype.card F : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  linarith

theorem finite_field_unit_cubic_fourth_sharp
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) {a : F} (ha : a ≠ 0) :
    ‖finiteFieldUnitCubicSum ψ a‖ ^ 4 ≤ 81 * (Fintype.card F : ℝ) ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (finite_field_unit_cubic_norm_le_three_sqrt ψ hψ ha) 4
  have hs : Real.sqrt (Fintype.card F : ℝ) ^ 4 = (Fintype.card F : ℝ) ^ 2 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [mul_pow, hs, show (3 : ℝ)^4 = 81 by norm_num] using h

theorem finite_field_cubic_eighth_sharp
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) {a : F} (ha : a ≠ 0) :
    ‖finiteFieldCubicSum ψ a‖ ^ 8 ≤ 256 * (Fintype.card F : ℝ) ^ 4 := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (finite_field_cubic_sum_norm_le_two_sqrt ψ hψ ha) 8
  have hs : Real.sqrt (Fintype.card F : ℝ) ^ 8 = (Fintype.card F : ℝ) ^ 4 := by
    rw [show 8 = 2 * 4 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [mul_pow, hs, show (2 : ℝ)^8 = 256 by norm_num] using h

theorem finite_field_four_unit_cubic_error_abs_sharp
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (b : F) :
    |(Fintype.card F : ℝ) * (finiteFieldFourUnitCubicCount F b : ℝ) -
        ((Fintype.card F : ℝ) - 1) ^ 4| ≤ 81 * (Fintype.card F : ℝ) ^ 3 := by
  have hnorm : ‖(Fintype.card F : ℂ) * (finiteFieldFourUnitCubicCount F b : ℂ) -
        ((Fintype.card F : ℂ) - 1) ^ 4‖ ≤ 81 * (Fintype.card F : ℝ) ^ 3 := by
    rw [← finite_field_four_unit_cubic_fourier_tail ψ hψ b]
    calc
      _ ≤ ∑ a ∈ (Finset.univ.erase (0 : F)),
          ‖finiteFieldUnitCubicSum ψ a ^ 4 * ψ (-a * b)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (Finset.univ.erase (0 : F)), 81 * (Fintype.card F : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro a ha
        simp only [norm_mul, norm_pow, finite_addChar_norm_one, mul_one]
        exact finite_field_unit_cubic_fourth_sharp ψ hψ (Finset.mem_erase.mp ha).1
      _ ≤ (Fintype.card F : ℝ) * (81 * (Fintype.card F : ℝ)^2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (Finset.erase_subset (0 : F) Finset.univ)
      _ = _ := by ring
  have he : (Fintype.card F : ℂ) * (finiteFieldFourUnitCubicCount F b : ℂ) -
      ((Fintype.card F : ℂ) - 1) ^ 4 =
      (((Fintype.card F : ℝ) * (finiteFieldFourUnitCubicCount F b : ℝ) -
        ((Fintype.card F : ℝ) - 1) ^ 4 : ℝ) : ℂ) := by push_cast; rfl
  simpa only [he, Complex.norm_real, Real.norm_eq_abs] using hnorm

theorem finite_field_four_unit_cubic_normalized_error_sharp (b : F) :
    |(finiteFieldFourUnitCubicCount F b : ℝ) / (Fintype.card F : ℝ)^3 -
      (1 - 1 / (Fintype.card F : ℝ))^4| ≤ 81 / (Fintype.card F : ℝ) := by
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have h := finite_field_four_unit_cubic_error_abs_sharp ψ hψ b
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card F : ℝ) * (finiteFieldFourUnitCubicCount F b : ℝ) -
      ((Fintype.card F : ℝ) - 1)^4 = (Fintype.card F : ℝ)^4 *
      ((finiteFieldFourUnitCubicCount F b : ℝ) / (Fintype.card F : ℝ)^3 -
        (1 - 1 / (Fintype.card F : ℝ))^4) := by field_simp
  rw [he, abs_mul, abs_of_pos (pow_pos hq 4)] at h
  apply (le_div_iff₀ hq).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hq 3)).mp
  convert h using 1 <;> ring

/-- In particular the manuscript's residue-norm cutoff 173 is sufficient. -/
theorem finite_field_four_unit_cubic_normalized_lower_173
    (hq : 173 ≤ Fintype.card F) (b : F) :
    (1 / 2 : ℝ) ≤ (finiteFieldFourUnitCubicCount F b : ℝ) /
      (Fintype.card F : ℝ)^3 := by
  have hqR : (173 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  have hqpos : 0 < (Fintype.card F : ℝ) := by linarith
  have hinv : 1 / (Fintype.card F : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hqpos).mpr
    linarith
  have hbase : 1 - 4 / (Fintype.card F : ℝ) ≤
      (1 - 1 / (Fintype.card F : ℝ))^4 := by
    have h := one_add_mul_le_pow
      (show (-2 : ℝ) ≤ -(1 / (Fintype.card F : ℝ)) by linarith) 4
    convert h using 1 <;> norm_num <;> ring
  have herr := (abs_le.mp (finite_field_four_unit_cubic_normalized_error_sharp b)).1
  have hsmall : 85 / (Fintype.card F : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hqpos).mpr
    linarith
  simp only [div_eq_mul_inv, one_mul] at hbase herr hsmall ⊢
  linarith

theorem finite_field_eight_cubes_normalized_error_sharp (b : F) :
    |(finiteFieldCubicSolutionCount F 8 b : ℝ) / (Fintype.card F : ℝ)^7 - 1| ≤
      256 / (Fintype.card F : ℝ)^3 := by
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have hnorm := finite_field_cubic_eight_error_norm_le ψ hψ b
  have hsum : (∑ a ∈ (Finset.univ.erase (0 : F)), ‖finiteFieldCubicSum ψ a‖^8) ≤
      256 * (Fintype.card F : ℝ)^5 := by
    calc
      _ ≤ ∑ _a ∈ (Finset.univ.erase (0 : F)), 256 * (Fintype.card F : ℝ)^4 := by
        apply Finset.sum_le_sum
        intro a ha
        exact finite_field_cubic_eighth_sharp ψ hψ (Finset.mem_erase.mp ha).1
      _ ≤ (Fintype.card F : ℝ) * (256 * (Fintype.card F : ℝ)^4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (Finset.erase_subset (0 : F) Finset.univ)
      _ = _ := by ring
  have h := hnorm.trans hsum
  have hec : (Fintype.card F : ℂ) * (finiteFieldCubicSolutionCount F 8 b : ℂ) -
      (Fintype.card F : ℂ)^8 =
      (((Fintype.card F : ℝ) * (finiteFieldCubicSolutionCount F 8 b : ℝ) -
        (Fintype.card F : ℝ)^8 : ℝ) : ℂ) := by push_cast; rfl
  rw [hec, Complex.norm_real, Real.norm_eq_abs] at h
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card F : ℝ) * (finiteFieldCubicSolutionCount F 8 b : ℝ) -
      (Fintype.card F : ℝ)^8 = (Fintype.card F : ℝ)^8 *
      ((finiteFieldCubicSolutionCount F 8 b : ℝ) / (Fintype.card F : ℝ)^7 - 1) := by
    field_simp
  rw [he, abs_mul, abs_of_pos (pow_pos hq 8)] at h
  apply (le_div_iff₀ (pow_pos hq 3)).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hq 5)).mp
  convert h using 1 <;> ring

end WaringSiegel

#print axioms WaringSiegel.finite_field_four_unit_cubic_normalized_lower_173
#print axioms WaringSiegel.finite_field_eight_cubes_normalized_error_sharp
