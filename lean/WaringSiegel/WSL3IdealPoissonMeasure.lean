import WaringSiegel.WSL3IdealPoissonAuxiliaryNormalization
import WaringSiegel.WSL3UnitSmoothNormalization

/-!
# Exact trace-dual coordinate measure and auxiliary main-term normalization

The paired frequency measure is proved to be coordinate Lebesgue measure
for the actual inverse-different basis. Combining it with the eight source
covolumes gives precisely the existing lattice-normalized singular integral.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem inverseDifferent_basisCovolume_inv :
    (basisCovolume (archimedeanTraceDualBasis (K:=K)))⁻¹ =
      (4:ℝ)^nrComplexPlaces K * basisCovolume (NumberField.mixedEmbedding.latticeBasis K) := by
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  let d := basisCovolume (archimedeanTraceDualBasis (K:=K))
  have hc : c ≠ 0 := (basisCovolume_pos _).ne'
  have he : d = (c*d)*c⁻¹ := by field_simp
  change d⁻¹ = (4:ℝ)^nrComplexPlaces K*c
  calc
    _ = ((c*d)*c⁻¹)⁻¹ := congrArg Inv.inv he
    _ = (((4:ℝ)^nrComplexPlaces K)⁻¹*c⁻¹)⁻¹ := by
      rw [show c*d = ((4:ℝ)^nrComplexPlaces K)⁻¹ from trace_lattice_covolume_product]
    _ = _ := by rw [mul_inv,inv_inv,inv_inv]

/-- The paired trace measure is literally inverse-different basis volume. -/
theorem integerLatticeDualMeasure_eq_map :
    archimedeanDualMeasure (integerLatticeSourceScale K) =
      Measure.map (archimedeanTraceDualBasis (K:=K)).equivFunL.symm volume := by
  rw [basis_map_volume,archimedeanDualMeasure,integerLatticeSourceScale,
    inverseDifferent_basisCovolume_inv,div_inv_eq_mul]

/-- Its actual trace-dual fundamental domain has volume one. -/
theorem integerLatticeDualMeasure_fundamentalDomain :
    archimedeanDualMeasure (integerLatticeSourceScale K)
      (ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K:=K))) = 1 := by
  rw [integerLatticeDualMeasure_eq_map]
  exact basis_map_volume_fundamentalDomain (archimedeanTraceDualBasis (K:=K))

/-- The actual auxiliary four-by-four zero coefficient. -/
def auxiliaryPoissonZeroCoefficient (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) : ℂ :=
  ((((auxiliaryCommonModulus c.1.1 p).absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
    auxiliaryMaskedTwistedComplete c p hp 0)^4 *
  (((c.1.1.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
    auxiliaryScaledTwistedComplete c p 0)^4 * c.2.1 (-Ideal.Quotient.mk c.1.1 ν)

theorem auxiliaryPoissonZeroCoefficient_eq (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    auxiliaryPoissonZeroCoefficient c p hp ν =
      (integerLatticeSourceScale K)^8 • auxiliaryCubicCharacterContribution c p hp ν :=
  auxiliaryPoisson_eight_zero_term c p hp ν

/-- Exact main-coefficient normalization after trace-dual coordinate integration.
The auxiliary arithmetic contribution multiplies the already proved positive
lattice-normalized singular integral, with no missing 2 or discriminant factor. -/
theorem auxiliaryPoisson_main_integral_normalization (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) (w : mixedSpace K → ℝ) (b : mixedSpace K) :
    (basisCovolume (archimedeanTraceDualBasis (K:=K)))⁻¹ •
      (auxiliaryPoissonZeroCoefficient c p hp ν * weightedSingularIntegral 3 8 w b) =
        auxiliaryCubicCharacterContribution c p hp ν *
          pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8 w b := by
  rw [auxiliaryPoissonZeroCoefficient_eq,pairedWeightedSingularIntegral_eq _ integerLatticeSourceScale_pos,
    inverseDifferent_basisCovolume_inv]
  simp only [integerLatticeSourceScale,div_inv_eq_mul,Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv]
  ring

#print axioms integerLatticeDualMeasure_eq_map
#print axioms auxiliaryPoisson_main_integral_normalization
end WaringSiegel.WSL3Poisson
