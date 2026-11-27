import WaringSiegel.WSL2MomentSimplePrimes
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Discriminant
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Integral primitive generators and a nonzero conductor obstruction

The discriminant of an integral primitive power basis supplies an actual
nonzero rational integer in the conductor of its order.
-/

noncomputable section
open Polynomial Algebra IntermediateField
open scoped NumberField nonZeroDivisors

namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem exists_integral_primitive_powerBasis :
    ∃ B : PowerBasis ℚ K, IsIntegral ℤ B.gen := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  obtain ⟨m, hm⟩ :=
    (Algebra.IsIntegral.isIntegral (R := ℚ) α).exists_multiple_integral_of_isLocalization
      (R := ℤ) (Rₘ := ℚ) ℤ⁰ α
  let θ : K := m • α
  have hm0 : ((m : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp m.property)
  have hθ : ℚ⟮θ⟯ = ⊤ := by
    apply top_le_iff.mp
    rw [← hα]
    apply adjoin_simple_le_iff.mpr
    have h := (ℚ⟮θ⟯).smul_mem (mem_adjoin_simple_self ℚ θ)
      (x := (((m : ℤ) : ℚ)⁻¹))
    simpa only [θ, Submonoid.smul_def, ← Int.cast_smul_eq_zsmul ℚ,
      smul_smul, inv_mul_cancel₀ hm0, one_smul] using h
  let B : PowerBasis ℚ K :=
    (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := ℚ) θ)).map
      ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)
  refine ⟨B, ?_⟩
  change IsIntegral ℤ θ
  exact hm

theorem integral_powerBasis_integer_discriminant
    (B : PowerBasis ℚ K) (hB : IsIntegral ℤ B.gen) :
    ∃ D : ℤ, D ≠ 0 ∧ (D : ℚ) = Algebra.discr ℚ B.basis := by
  have hi : IsIntegral ℤ (Algebra.discr ℚ B.basis) :=
    Algebra.discr_isIntegral ℚ (fun i => by
      rw [B.basis_eq_pow]
      exact hB.pow _)
  obtain ⟨D, hD⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  refine ⟨D, ?_, hD⟩
  intro hzero
  apply Algebra.discr_not_zero_of_basis ℚ B.basis
  rw [← hD, hzero, map_zero]

theorem integer_discriminant_mem_conductor
    (B : PowerBasis ℚ K) (hB : IsIntegral ℤ B.gen)
    (D : ℤ) (hD : (D : ℚ) = Algebra.discr ℚ B.basis) :
    (D : 𝓞 K) ∈ conductor ℤ (⟨B.gen, hB⟩ : 𝓞 K) := by
  rw [mem_conductor_iff]
  intro z
  let f : 𝓞 K →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hB z.property
  rw [← hD] at hz
  have hmap : f ((D : 𝓞 K) * z) ∈
      (Algebra.adjoin ℤ ({⟨B.gen, hB⟩} : Set (𝓞 K))).map f := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    simpa [f, Algebra.smul_def] using hz
  obtain ⟨w, hw, heq⟩ := hmap
  have hw' : w = (D : 𝓞 K) * z :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K) heq
  simpa only [hw'] using hw

theorem exists_integral_generator_nonzero_exponent :
    ∃ θ : 𝓞 K, RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨B, hB⟩ := exists_integral_primitive_powerBasis (K := K)
  obtain ⟨D, hD0, hD⟩ := integral_powerBasis_integer_discriminant B hB
  let θ : 𝓞 K := ⟨B.gen, hB⟩
  refine ⟨θ, ?_⟩
  change Ideal.absNorm (Ideal.under ℤ (conductor ℤ θ)) ≠ 0
  intro hzero
  have hbot : Ideal.under ℤ (conductor ℤ θ) = ⊥ := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ θ)), hzero]
    simp
  have hmem : D ∈ Ideal.under ℤ (conductor ℤ θ) :=
    integer_discriminant_mem_conductor B hB D hD
  rw [hbot, Ideal.mem_bot] at hmem
  exact hD0 hmem

end WaringSiegel.WSL3
