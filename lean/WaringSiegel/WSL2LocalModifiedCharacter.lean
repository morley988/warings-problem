import WaringSiegel.WSL2LocalOriginalModified

/-!
# The finite-character formula for the modified local factor

This interface identifies the proved positive factor with the normalized
four-unit complete character sum, retaining the (1-q⁻¹)^4 zero-frequency
term. It does not assert a global major-arc expansion.
-/

noncomputable section
open IsLocalRing
open scoped NumberField BigOperators Classical

namespace WaringSiegel

/-- Exact normalized finite-field character formula for the modified factor. -/
theorem finite_field_four_unit_normalized_character_sum
    {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (b : F) :
    (∑ a : F, (finiteFieldUnitCubicSum ψ a / (Fintype.card F : ℂ)) ^ 4 * ψ (-a * b)) =
      (finiteFieldFourUnitCubicCount F b : ℂ) / (Fintype.card F : ℂ) ^ 3 := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [div_pow, div_mul_eq_mul_div]
  rw [← Finset.sum_div, finite_field_four_unit_cubic_fourier_count ψ hψ]
  field_simp

/-- The zero-frequency term is the fourth power of the proportion of units. -/
theorem finite_field_four_unit_zero_frequency
    {F : Type*} [Field F] [Fintype F] (ψ : AddChar F ℂ) :
    (finiteFieldUnitCubicSum ψ 0 / (Fintype.card F : ℂ)) ^ 4 =
      (1 - 1 / (Fintype.card F : ℂ)) ^ 4 := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [finite_field_unit_cubic_sum_eq, finite_field_cubic_sum_zero]
  congr 1
  field_simp

variable {K : Type*} [Field K] [NumberField K]

/-- In the actual completion residue field the normalized character formula
is exactly the modified factor used in the uniform auxiliary-prime product. -/
theorem completion_modified_factor_character_formula
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [Fintype (ResidueField (v.adicCompletionIntegers K))]
    (ψ : AddChar (ResidueField (v.adicCompletionIntegers K)) ℂ)
    (hψ : ψ.IsPrimitive) (ν : 𝓞 K) :
    (cubicModifiedResidueFactor v ν : ℂ) =
      ∑ a : ResidueField (v.adicCompletionIntegers K),
        (finiteFieldUnitCubicSum ψ a / (Ideal.absNorm v.asIdeal : ℂ)) ^ 4 *
          ψ (-a * residue (v.adicCompletionIntegers K)
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) := by
  have hcard : Fintype.card (ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, completion_residue_card_eq_absNorm]
  rw [← hcard, finite_field_four_unit_normalized_character_sum ψ hψ]
  unfold cubicModifiedResidueFactor
  push_cast
  rw [hcard]

end WaringSiegel

#print axioms WaringSiegel.finite_field_four_unit_normalized_character_sum
#print axioms WaringSiegel.completion_modified_factor_character_formula
