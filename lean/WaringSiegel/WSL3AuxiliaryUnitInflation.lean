import WaringSiegel.WSL3AuxiliaryQuotientUnits
import WaringSiegel.WSL3RestrictedResidueMass

/-! # WSL3: normalized unit sums descend through nilpotent quotient kernels -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem finite_unit_power_average_inflation
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (n : ℕ) (hJI : J^n ≤ I) [Fintype (R ⧸ I)] [Fintype (R ⧸ J)]
    (ψ : AddChar (R ⧸ J) ℂ) (k : ℕ) :
    finiteRingUnitPowerSum
      (ψ.compAddMonoidHom (Ideal.Quotient.factor hIJ).toAddMonoidHom) k /
        (Fintype.card (R ⧸ I) : ℂ) =
      finiteRingUnitPowerSum ψ k / (Fintype.card (R ⧸ J) : ℂ) := by
  have h := finite_masked_power_average_inflation (Ideal.Quotient.factor hIJ)
    (Ideal.Quotient.factor_surjective hIJ) (RingHom.id (R ⧸ J)) ψ k
  simp only [RingHom.id_comp, finiteMaskedPowerSum_id] at h
  rw [finiteMaskedPowerSum_factor_of_power_le I J hIJ n hJI] at h
  exact h

theorem finite_restricted_cubic_character_inflation
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (n : ℕ) (hJI : J^n ≤ I) [Fintype (R ⧸ I)] [Fintype (R ⧸ J)]
    (ψ : AddChar (R ⧸ J) ℂ) (p b : R ⧸ I) :
    finiteRingRestrictedCubicCharacterTerm p b
      (ψ.compAddMonoidHom (Ideal.Quotient.factor hIJ).toAddMonoidHom) =
      finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.factor hIJ p)
        (Ideal.Quotient.factor hIJ b) ψ := by
  unfold finiteRingRestrictedCubicCharacterTerm
  rw [finite_unit_power_average_inflation I J hIJ n hJI,
    finite_scaled_power_average_inflation (Ideal.Quotient.factor hIJ)
      (Ideal.Quotient.factor_surjective hIJ)]
  change _ * ψ (Ideal.Quotient.factor hIJ (-b)) =
    _ * ψ (-(Ideal.Quotient.factor hIJ b))
  rw [(Ideal.Quotient.factor hIJ).map_neg]

theorem finite_field_unit_average_trivial
    {F : Type*} [Field F] [Fintype F] (k : ℕ) :
    finiteRingUnitPowerSum (1 : AddChar F ℂ) k / (Fintype.card F : ℂ) =
      1 - 1/(Fintype.card F : ℂ) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteRingUnitPowerSum, AddChar.one_apply, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_units,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero), Nat.cast_one]
  field_simp

theorem finite_field_restricted_trivial_coefficient
    {F : Type*} [Field F] [Fintype F] (b : F) :
    finiteRingRestrictedCubicCharacterTerm (0 : F) b (1 : AddChar F ℂ) =
      (1 - 1/(Fintype.card F : ℂ))^4 := by
  rw [finiteRingRestrictedCubicCharacterTerm_zero_scale,
    finite_field_unit_average_trivial, AddChar.one_apply, mul_one]

end WaringSiegel
#print axioms WaringSiegel.finite_restricted_cubic_character_inflation
#print axioms WaringSiegel.finite_field_restricted_trivial_coefficient
