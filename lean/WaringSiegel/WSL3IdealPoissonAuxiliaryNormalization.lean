import WaringSiegel.WSL3IdealPoissonAuxiliary

/-!
# Exact auxiliary Poisson main-coefficient normalization

Quotient cardinalities are identified with ideal norms. The two actual
Poisson zero terms are U/covol(O_K) and G/covol(O_K), so the eight-variable
coefficient carries exactly covol(O_K)^(-8), before torus integration.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem ideal_quotient_card_eq_absNorm (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
    Fintype.card (𝓞 K ⧸ I) = I.absNorm := by
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem auxiliaryMaskedTwistedComplete_zero_norm (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) :
    auxiliaryMaskedTwistedComplete c p hp 0 / ((auxiliaryCommonModulus c.1.1 p).absNorm:ℂ) =
      auxiliaryMaskedCubicAverage c p hp := by
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  have h := auxiliaryMaskedTwistedComplete_zero c p hp
  simpa only [ideal_quotient_card_eq_absNorm] using h

theorem auxiliaryScaledTwistedComplete_zero_norm (c : CubicConductorCharacter K) (p : 𝓞 K) :
    auxiliaryScaledTwistedComplete c p 0 / (c.1.1.absNorm:ℂ) = auxiliaryScaledCubicAverage c p := by
  letI := idealResidueFintype c.1.1 c.1.2
  simpa only [ideal_quotient_card_eq_absNorm] using auxiliaryScaledTwistedComplete_zero c p

private theorem real_covolume_inverse_smul (N : ℕ) (a : ℝ) (z : ℂ) :
    ((N:ℝ)*a)⁻¹ • z = a⁻¹ • (z/(N:ℂ)) := by
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_natCast,div_eq_mul_inv,mul_inv]
  ring

theorem auxiliaryMaskedPoisson_zero_term (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) :
    (((auxiliaryCommonModulus c.1.1 p).absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
      auxiliaryMaskedTwistedComplete c p hp 0 =
        (basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ • auxiliaryMaskedCubicAverage c p hp := by
  rw [real_covolume_inverse_smul,auxiliaryMaskedTwistedComplete_zero_norm]

theorem auxiliaryScaledPoisson_zero_term (c : CubicConductorCharacter K) (p : 𝓞 K) :
    ((c.1.1.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
      auxiliaryScaledTwistedComplete c p 0 =
        (basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ • auxiliaryScaledCubicAverage c p := by
  rw [real_covolume_inverse_smul,auxiliaryScaledTwistedComplete_zero_norm]

/-- The literal four-by-four Poisson zero coefficient, before integrating
over the trace torus, has exactly the eighth inverse covolume factor. -/
theorem auxiliaryPoisson_eight_zero_term (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    ((((auxiliaryCommonModulus c.1.1 p).absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
      auxiliaryMaskedTwistedComplete c p hp 0)^4 *
    (((c.1.1.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
      auxiliaryScaledTwistedComplete c p 0)^4 * c.2.1 (-Ideal.Quotient.mk c.1.1 ν) =
        (basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹^8 •
          auxiliaryCubicCharacterContribution c p hp ν := by
  rw [auxiliaryMaskedPoisson_zero_term,auxiliaryScaledPoisson_zero_term]
  simp only [auxiliaryCubicCharacterContribution,Complex.real_smul,Complex.ofReal_pow]
  ring

#print axioms auxiliaryMaskedPoisson_zero_term
#print axioms auxiliaryScaledPoisson_zero_term
#print axioms auxiliaryPoisson_eight_zero_term
end WaringSiegel.WSL3Poisson
