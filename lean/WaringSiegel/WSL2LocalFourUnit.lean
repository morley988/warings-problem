import WaringSiegel.WSL2LocalFiniteFourier

/-!
# Four-unit cubic modified factors over large finite fields

Elementary differencing suffices for a uniform positive lower bound. The
proved error has order q^(-1/2), so the explicit positivity threshold is
larger than the manuscript's threshold obtained from a Weil estimate.
-/

noncomputable section
set_option maxHeartbeats 0
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel

variable {F : Type*} [Field F] [Fintype F]

def finiteFieldUnitCubicSum (ψ : AddChar F ℂ) (a : F) : ℂ :=
  ∑ x : Fˣ, ψ (a * (x : F) ^ 3)

def finiteFieldFourUnitCubicCount (F : Type*) [Field F] (b : F) : ℕ :=
  Nat.card {x : Fin 4 → Fˣ // (∑ i, (x i : F) ^ 3) = b}

theorem finite_field_unit_cubic_sum_eq (ψ : AddChar F ℂ) (a : F) :
    finiteFieldUnitCubicSum ψ a = finiteFieldCubicSum ψ a - 1 := by
  unfold finiteFieldUnitCubicSum
  trans ∑ x ∈ (Finset.univ.erase (0 : F)), ψ (a * x ^ 3)
  · apply Finset.sum_bij (fun (x : Fˣ) _ => (x : F))
    · intro x _; simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact Units.ne_zero x
    · intro x _ y _ h; exact Units.ext h
    · intro x hx; exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
    · intro x _; rfl
  · rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F))]
    simp only [zero_pow (by decide : 3 ≠ 0), mul_zero, ψ.map_zero_eq_one]
    rfl

theorem finite_field_unit_cubic_norm_le (ψ : AddChar F ℂ) (a : F) :
    ‖finiteFieldUnitCubicSum ψ a‖ ≤ ‖finiteFieldCubicSum ψ a‖ + 1 := by
  rw [finite_field_unit_cubic_sum_eq]
  simpa only [norm_one] using norm_sub_le (finiteFieldCubicSum ψ a) (1 : ℂ)

theorem finite_field_unit_cubic_fourth
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h6 : (6 : F) ≠ 0)
    {a : F} (ha : a ≠ 0) :
    ‖finiteFieldUnitCubicSum ψ a‖ ^ 4 ≤ 24 * (Fintype.card F : ℝ) ^ 3 := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (finite_field_unit_cubic_norm_le ψ a) 4
  have hadd := add_pow_le (norm_nonneg (finiteFieldCubicSum ψ a)) (by norm_num : (0 : ℝ) ≤ 1) 4
  have hw := finite_field_cubic_weyl_fourth ψ hψ h6 ha
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq3 : (1 : ℝ) ≤ (Fintype.card F : ℝ) ^ 3 := one_le_pow₀ hq
  norm_num at hadd
  nlinarith

theorem finite_field_unit_cubic_second_moment
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ‖finiteFieldUnitCubicSum ψ a‖ ^ 2) ≤ 8 * (Fintype.card F : ℝ) ^ 2 := by
  have hlocal (a : F) : ‖finiteFieldUnitCubicSum ψ a‖ ^ 2 ≤
      2 * (‖finiteFieldCubicSum ψ a‖ ^ 2 + 1) := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (finite_field_unit_cubic_norm_le ψ a) 2
    have hadd := add_pow_le (norm_nonneg (finiteFieldCubicSum ψ a)) (by norm_num : (0 : ℝ) ≤ 1) 2
    norm_num at hadd
    exact hn.trans hadd
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset F)) => hlocal a)
  have h2 := finite_field_cubic_second_moment_le ψ hψ
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  nlinarith

/-- The fourth-power unit-sum tail is small enough to make four-unit counts positive. -/
theorem finite_field_unit_cubic_fourth_sum_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h6 : (6 : F) ≠ 0) :
    (∑ a ∈ (Finset.univ.erase (0 : F)), ‖finiteFieldUnitCubicSum ψ a‖ ^ 4) ^ 2 ≤
      1536 * (Fintype.card F : ℝ) ^ 7 := by
  let A : Finset F := Finset.univ.erase 0
  let t : F → ℝ := fun a => ‖finiteFieldUnitCubicSum ψ a‖
  have h2 : (∑ a ∈ A, t a ^ 2) ≤ 8 * (Fintype.card F : ℝ) ^ 2 := by
    apply le_trans _ (finite_field_unit_cubic_second_moment ψ hψ)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  have h6local (a : F) (ha : a ∈ A) : t a ^ 6 ≤
      24 * (Fintype.card F : ℝ) ^ 3 * t a ^ 2 := by
    have hw := finite_field_unit_cubic_fourth ψ hψ h6 (Finset.mem_erase.mp ha).1
    have hm := mul_le_mul_of_nonneg_right hw (sq_nonneg (t a))
    convert hm using 1 <;> dsimp [t] <;> ring
  have h6sum : (∑ a ∈ A, t a ^ 6) ≤ 192 * (Fintype.card F : ℝ) ^ 5 := by
    calc
      _ ≤ ∑ a ∈ A, 24 * (Fintype.card F : ℝ) ^ 3 * t a ^ 2 := Finset.sum_le_sum h6local
      _ = 24 * (Fintype.card F : ℝ) ^ 3 * ∑ a ∈ A, t a ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 24 * (Fintype.card F : ℝ) ^ 3 * (8 * (Fintype.card F : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A t (fun a => t a ^ 3)
  have hp (a : F) : t a * t a ^ 3 = t a ^ 4 := by ring
  have hsq (a : F) : (t a ^ 3) ^ 2 = t a ^ 6 := by ring
  simp only [hp, hsq] at hc
  change (∑ a ∈ A, t a ^ 4) ^ 2 ≤ _
  calc
    _ ≤ (∑ a ∈ A, t a ^ 2) * (∑ a ∈ A, t a ^ 6) := hc
    _ ≤ (8 * (Fintype.card F : ℝ) ^ 2) * (192 * (Fintype.card F : ℝ) ^ 5) :=
      mul_le_mul h2 h6sum (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = _ := by ring

theorem finite_field_unit_cubic_power_expansion
    (ψ : AddChar F ℂ) (a b : F) :
    finiteFieldUnitCubicSum ψ a ^ 4 * ψ (-a * b) =
      ∑ x : Fin 4 → Fˣ, ψ (a * ((∑ i, (x i : F) ^ 3) - b)) := by
  rw [finiteFieldUnitCubicSum, Fintype.sum_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  have hp : (∏ i, ψ (a * (x i : F) ^ 3)) = ψ (a * ∑ i, (x i : F) ^ 3) := by
    rw [Finset.mul_sum, finite_addChar_sum]
  rw [hp, ← ψ.map_add_eq_mul]
  congr 1
  ring

/-- Exact Fourier formula for the count of four unit cubes. -/
theorem finite_field_four_unit_cubic_fourier_count
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (b : F) :
    (∑ a : F, finiteFieldUnitCubicSum ψ a ^ 4 * ψ (-a * b)) =
      (Fintype.card F : ℂ) * (finiteFieldFourUnitCubicCount F b : ℂ) := by
  simp only [finite_field_unit_cubic_power_expansion]
  rw [Finset.sum_comm]
  simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero, apply_ite, Nat.cast_zero,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold finiteFieldFourUnitCubicCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

theorem finite_field_four_unit_cubic_fourier_tail
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (b : F) :
    (∑ a ∈ (Finset.univ.erase (0 : F)), finiteFieldUnitCubicSum ψ a ^ 4 * ψ (-a * b)) =
      (Fintype.card F : ℂ) * (finiteFieldFourUnitCubicCount F b : ℂ) -
        ((Fintype.card F : ℂ) - 1) ^ 4 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
    finite_field_four_unit_cubic_fourier_count ψ hψ]
  simp only [finite_field_unit_cubic_sum_eq, finite_field_cubic_sum_zero,
    neg_zero, zero_mul, ψ.map_zero_eq_one, mul_one]

theorem finite_field_four_unit_cubic_error_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h6 : (6 : F) ≠ 0) (b : F) :
    ((Fintype.card F : ℝ) * (finiteFieldFourUnitCubicCount F b : ℝ) -
      ((Fintype.card F : ℝ) - 1) ^ 4) ^ 2 ≤ 1536 * (Fintype.card F : ℝ) ^ 7 := by
  have hnorm : ‖(Fintype.card F : ℂ) * (finiteFieldFourUnitCubicCount F b : ℂ) -
        ((Fintype.card F : ℂ) - 1) ^ 4‖ ≤
      ∑ a ∈ (Finset.univ.erase (0 : F)), ‖finiteFieldUnitCubicSum ψ a‖ ^ 4 := by
    rw [← finite_field_four_unit_cubic_fourier_tail ψ hψ b]
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro a _
    simp only [norm_mul, norm_pow, finite_addChar_norm_one, mul_one, le_refl]
  have h := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (finite_field_unit_cubic_fourth_sum_sq ψ hψ h6)
  have he : (Fintype.card F : ℂ) * (finiteFieldFourUnitCubicCount F b : ℂ) -
      ((Fintype.card F : ℂ) - 1) ^ 4 =
      (((Fintype.card F : ℝ) * (finiteFieldFourUnitCubicCount F b : ℝ) -
        ((Fintype.card F : ℝ) - 1) ^ 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- A target-uniform squared error for the normalized four-unit modified factor. -/
theorem finite_field_four_unit_cubic_normalized_error_sq
    (h6 : (6 : F) ≠ 0) (b : F) :
    ((finiteFieldFourUnitCubicCount F b : ℝ) / (Fintype.card F : ℝ) ^ 3 -
      (1 - 1 / (Fintype.card F : ℝ)) ^ 4) ^ 2 ≤ 1536 / (Fintype.card F : ℝ) := by
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have h := finite_field_four_unit_cubic_error_sq ψ hψ h6 b
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card F : ℝ) * (finiteFieldFourUnitCubicCount F b : ℝ) -
      ((Fintype.card F : ℝ) - 1) ^ 4 =
      (Fintype.card F : ℝ) ^ 4 *
        ((finiteFieldFourUnitCubicCount F b : ℝ) / (Fintype.card F : ℝ) ^ 3 -
          (1 - 1 / (Fintype.card F : ℝ)) ^ 4) := by
    field_simp
  rw [he, mul_pow] at h
  apply (le_div_iff₀ hq).mpr
  apply (mul_le_mul_left (pow_pos hq 7)).mp
  convert h using 1 <;> ring

/-- Every target is a sum of four unit cubes, with a uniform quantitative
margin, once the residue field has at least 24576 elements and avoids 2,3. -/
theorem finite_field_four_unit_cubic_normalized_lower
    (h6 : (6 : F) ≠ 0) (hq : 24576 ≤ Fintype.card F) (b : F) :
    (1 / 2 : ℝ) ≤ (finiteFieldFourUnitCubicCount F b : ℝ) / (Fintype.card F : ℝ) ^ 3 := by
  have hqR : (24576 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  have hqpos : 0 < (Fintype.card F : ℝ) := by linarith
  have hsmall : 1536 / (Fintype.card F : ℝ) ≤ (1 / 4 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hqpos).mpr
    norm_num
    linarith
  have herr := (finite_field_four_unit_cubic_normalized_error_sq h6 b).trans hsmall
  have hinv : (0 : ℝ) ≤ 1 / (Fintype.card F : ℝ) := by positivity
  have hinvsmall : 1 / (Fintype.card F : ℝ) ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ hqpos).mpr
    linarith
  have hbaseline : (3 / 4 : ℝ) ≤ (1 - 1 / (Fintype.card F : ℝ)) ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15 / 16)
      (show (15 / 16 : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ) by linarith) 4
    exact (show (3 / 4 : ℝ) ≤ (15 / 16 : ℝ) ^ 4 by norm_num).trans hp
  have herrabs := abs_le_of_sq_le_sq herr (by norm_num : (0 : ℝ) ≤ 1 / 4)
  linarith [(abs_le.mp herrabs).1]

end WaringSiegel

#print axioms WaringSiegel.finite_field_unit_cubic_fourth_sum_sq

#print axioms WaringSiegel.finite_field_four_unit_cubic_normalized_lower
