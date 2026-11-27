import WaringSiegel.WSL3RestrictedAbsoluteCharacters

/-! # WSL3: the first auxiliary conductor level has absolute mass at most 81/q -/
noncomputable section
set_option maxHeartbeats 500000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {F : Type*} [Field F] [Fintype F]

theorem finiteRingUnitPowerSum_three_eq (ψ : AddChar F ℂ) :
    finiteRingUnitPowerSum ψ 3 = finiteFieldUnitCubicSum ψ 1 := by
  simp only [finiteRingUnitPowerSum, finiteFieldUnitCubicSum, one_mul]

theorem finiteRingRestrictedCubicCharacterTerm_zero_scale (ψ : AddChar F ℂ) (b : F) :
    finiteRingRestrictedCubicCharacterTerm (0 : F) b ψ =
      (finiteRingUnitPowerSum ψ 3 / (Fintype.card F : ℂ))^4 * ψ (-b) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteRingRestrictedCubicCharacterTerm, finiteRingScaledPowerSum,
    zero_mul, zero_pow (by decide : 3 ≠ 0), ψ.map_zero_eq_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self hq, one_pow]

theorem finite_field_restricted_character_norm_le (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (b : F) :
    ‖finiteRingRestrictedCubicCharacterTerm (0 : F) b ψ‖ ≤
      81 / (Fintype.card F : ℝ)^2 := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := finite_field_unit_cubic_fourth_sharp ψ (AddChar.IsPrimitive.of_ne_one hψ)
    (by exact one_ne_zero : (1 : F) ≠ 0)
  rw [finiteRingRestrictedCubicCharacterTerm_zero_scale,
    finiteRingUnitPowerSum_three_eq, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, ψ.norm_apply, mul_one, div_pow]
  apply (div_le_div_iff₀ (pow_pos hq 4) (pow_pos hq 2)).mpr
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg hq.le 2)
  convert hh using 1 <;> ring

theorem finite_field_restricted_primitive_absolute_mass (b : F) :
    (∑ ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)),
      ‖finiteRingRestrictedCubicCharacterTerm (0 : F) b ψ‖) ≤
        81 / (Fintype.card F : ℝ) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ∑ _ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)), 81 / (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro ψ hψ
      exact finite_field_restricted_character_norm_le ψ (Finset.mem_erase.mp hψ).1 b
    _ ≤ (Fintype.card F : ℝ) * (81 / (Fintype.card F : ℝ)^2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard := Finset.card_le_card (Finset.erase_subset (1 : AddChar F ℂ) Finset.univ)
      simpa only [Finset.card_univ, AddChar.card_eq] using (Nat.cast_le (α := ℝ)).mpr hcard
    _ = _ := by field_simp

/-- Including its nonunit-density zero mode, the modified residue factor
has conductor-weighted absolute mass at most q squared. -/
theorem finite_field_restricted_weighted_mass_le_square
    (hq173 : 173 ≤ Fintype.card F) (b : F) :
    (1 - 1/(Fintype.card F : ℝ))^4 +
      (Fintype.card F : ℝ)^(5/4 : ℝ) *
        (∑ ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)),
          ‖finiteRingRestrictedCubicCharacterTerm (0 : F) b ψ‖) ≤
        (Fintype.card F : ℝ)^2 := by
  have hq : (173 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq173
  have hq0 : 0 < (Fintype.card F : ℝ) := by linarith
  have hq1 : 1 ≤ (Fintype.card F : ℝ) := by linarith
  have hinv : 1/(Fintype.card F : ℝ) ≤ 1 :=
    (div_le_one hq0).mpr hq1
  have hsub : 1-1/(Fintype.card F : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  have hbase : (1 - 1/(Fintype.card F : ℝ))^4 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by linarith : 0 ≤ 1-1/(Fintype.card F : ℝ))
      hsub 4
  have hw : (Fintype.card F : ℝ)^(5/4 : ℝ) ≤ (Fintype.card F : ℝ)^2 := by
    rw [← Real.rpow_natCast (Fintype.card F : ℝ) 2]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hb : (Fintype.card F : ℝ)^(5/4 : ℝ) *
      (∑ ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)),
        ‖finiteRingRestrictedCubicCharacterTerm (0 : F) b ψ‖) ≤
      81*(Fintype.card F : ℝ) := by
    calc
      _ ≤ (Fintype.card F : ℝ)^2 * (81/(Fintype.card F : ℝ)) :=
        mul_le_mul hw (finite_field_restricted_primitive_absolute_mass b)
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
      _ = _ := by field_simp
  nlinarith [sq_nonneg ((Fintype.card F : ℝ)-82)]

end WaringSiegel
#print axioms WaringSiegel.finite_field_restricted_primitive_absolute_mass

#print axioms WaringSiegel.finite_field_restricted_weighted_mass_le_square
