import WaringSiegel.WSL3IdealPoissonCubic
import WaringSiegel.WSL3AuxiliaryInflation

/-!
# Literal auxiliary unit-mask and scaled-cube Poisson formulas

The masked modulus is exactly I intersect (p). The only unit condition is
in O_K/(p). Normalized zero Fourier coefficients are identified with the
existing actual U and G averages, and their four-by-four product is the
existing auxiliary cubic character contribution.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryMaskedResidueWeight (c : CubicConductorCharacter K) (p : 𝓞 K) :
    (𝓞 K ⧸ auxiliaryCommonModulus c.1.1 p) → ℂ :=
  let f : (𝓞 K ⧸ auxiliaryCommonModulus c.1.1 p) →+* (𝓞 K ⧸ c.1.1) := Ideal.Quotient.factor inf_le_left
  let g : (𝓞 K ⧸ auxiliaryCommonModulus c.1.1 p) →+* (𝓞 K ⧸ Ideal.span ({p}:Set (𝓞 K))) :=
    Ideal.Quotient.factor inf_le_right
  fun q => if IsUnit (g q) then c.2.1 ((f q)^3) else 0

def auxiliaryScaledResidueWeight (c : CubicConductorCharacter K) (p : 𝓞 K) :
    (𝓞 K ⧸ c.1.1) → ℂ :=
  fun q => c.2.1 ((Ideal.Quotient.mk c.1.1 p*q)^3)

theorem auxiliaryMaskedResidueWeight_mk (c : CubicConductorCharacter K) (p x : 𝓞 K) :
    auxiliaryMaskedResidueWeight c p (Ideal.Quotient.mk (auxiliaryCommonModulus c.1.1 p) x) =
      if IsUnit (Ideal.Quotient.mk (Ideal.span ({p}:Set (𝓞 K))) x)
        then c.2.1 (Ideal.Quotient.mk c.1.1 (x^3)) else 0 := by
  simp only [auxiliaryMaskedResidueWeight,Ideal.Quotient.factor_mk,(Ideal.Quotient.mk c.1.1).map_pow]

theorem auxiliaryScaledResidueWeight_mk (c : CubicConductorCharacter K) (p x : 𝓞 K) :
    auxiliaryScaledResidueWeight c p (Ideal.Quotient.mk c.1.1 x) =
      c.2.1 (Ideal.Quotient.mk c.1.1 ((p*x)^3)) := by
  simp only [auxiliaryScaledResidueWeight,(Ideal.Quotient.mk c.1.1).map_pow,
    (Ideal.Quotient.mk c.1.1).map_mul]

def auxiliaryMaskedTwistedComplete (c : CubicConductorCharacter K) (p : 𝓞 K) (hp : p ≠ 0)
    (ξ : mixedSpace K) : ℂ :=
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  idealCompleteTraceFactor M (auxiliaryMaskedResidueWeight c p) ξ

def auxiliaryScaledTwistedComplete (c : CubicConductorCharacter K) (p : 𝓞 K)
    (ξ : mixedSpace K) : ℂ :=
  letI := idealResidueFintype c.1.1 c.1.2
  idealCompleteTraceFactor c.1.1 (auxiliaryScaledResidueWeight c p) ξ

/-- The zero dual frequency is exactly the actual normalized auxiliary U. -/
theorem auxiliaryMaskedTwistedComplete_zero (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) :
    let M := auxiliaryCommonModulus c.1.1 p
    letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
    auxiliaryMaskedTwistedComplete c p hp 0 / (Fintype.card (𝓞 K ⧸ M):ℂ) =
      auxiliaryMaskedCubicAverage c p hp := by
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ c.1.1) := Ideal.Quotient.factor inf_le_left
  unfold auxiliaryMaskedTwistedComplete idealCompleteTraceFactor auxiliaryMaskedCubicAverage finiteMaskedPowerSum
  simp only [archimedeanTraceCharacter,zero_mul,map_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  change (∑ q : 𝓞 K ⧸ M, auxiliaryMaskedResidueWeight c p q)/(Fintype.card (𝓞 K ⧸ M):ℂ) =
    (∑ q : 𝓞 K ⧸ M,
      if IsUnit ((Ideal.Quotient.factor (show M ≤ Ideal.span ({p}:Set (𝓞 K)) from inf_le_right)) q)
      then c.2.1 (f (q^3)) else 0)/(Fintype.card (𝓞 K ⧸ M):ℂ)
  simp only [f.map_pow]
  rfl

/-- The zero dual frequency is exactly the actual normalized auxiliary G. -/
theorem auxiliaryScaledTwistedComplete_zero (c : CubicConductorCharacter K) (p : 𝓞 K) :
    letI := idealResidueFintype c.1.1 c.1.2
    auxiliaryScaledTwistedComplete c p 0 / (Fintype.card (𝓞 K ⧸ c.1.1):ℂ) =
      auxiliaryScaledCubicAverage c p := by
  letI := idealResidueFintype c.1.1 c.1.2
  simp only [auxiliaryScaledTwistedComplete,idealCompleteTraceFactor,auxiliaryScaledCubicAverage,
    finiteRingScaledPowerSum,auxiliaryScaledResidueWeight,archimedeanTraceCharacter,zero_mul,
    map_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]

/-- The existing literal auxiliary eight-cube term is exactly the product
of the two actual Poisson zero-frequency coefficients with the target phase. -/
theorem auxiliaryPoisson_zero_coefficients (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    let M := auxiliaryCommonModulus c.1.1 p
    letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
    letI := idealResidueFintype c.1.1 c.1.2
    (auxiliaryMaskedTwistedComplete c p hp 0/(Fintype.card (𝓞 K ⧸ M):ℂ))^4 *
      (auxiliaryScaledTwistedComplete c p 0/(Fintype.card (𝓞 K ⧸ c.1.1):ℂ))^4 *
      c.2.1 (-Ideal.Quotient.mk c.1.1 ν) = auxiliaryCubicCharacterContribution c p hp ν := by
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  letI := idealResidueFintype c.1.1 c.1.2
  change (auxiliaryMaskedTwistedComplete c p hp 0/(Fintype.card (𝓞 K ⧸ M):ℂ))^4 *
    (auxiliaryScaledTwistedComplete c p 0/(Fintype.card (𝓞 K ⧸ c.1.1):ℂ))^4 *
    c.2.1 (-Ideal.Quotient.mk c.1.1 ν) = auxiliaryCubicCharacterContribution c p hp ν
  rw [auxiliaryMaskedTwistedComplete_zero c p hp,auxiliaryScaledTwistedComplete_zero c p]
  rfl

/-- Exact masked-source Poisson: only the quotient modulo p imposes units. -/
theorem poisson_auxiliary_masked_source (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : 𝓞 K,
      if IsUnit (Ideal.Quotient.mk (Ideal.span ({p}:Set (𝓞 K))) x)
      then c.2.1 (Ideal.Quotient.mk c.1.1 (x^3))*f (mixedEmbedding K (x:K)) else 0) =
      (((auxiliaryCommonModulus c.1.1 p).absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' ξ : (inverseDifferent K * (auxiliaryCommonModulus c.1.1 p : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          auxiliaryMaskedTwistedComplete c p hp (mixedEmbedding K (ξ:K))*traceFourier f (mixedEmbedding K (ξ:K))) := by
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  have h := poisson_ideal_residue_weight M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
    (auxiliaryMaskedResidueWeight c p) f
  simpa only [M,auxiliaryMaskedResidueWeight_mk,ite_mul,zero_mul,auxiliaryMaskedTwistedComplete] using h

/-- Exact scaled-cube source Poisson on the true conductor quotient. -/
theorem poisson_auxiliary_scaled_source (c : CubicConductorCharacter K)
    (p : 𝓞 K) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : 𝓞 K, c.2.1 (Ideal.Quotient.mk c.1.1 ((p*x)^3))*f (mixedEmbedding K (x:K))) =
      ((c.1.1.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' ξ : (inverseDifferent K * (c.1.1 : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          auxiliaryScaledTwistedComplete c p (mixedEmbedding K (ξ:K))*traceFourier f (mixedEmbedding K (ξ:K))) := by
  letI := idealResidueFintype c.1.1 c.1.2
  have h := poisson_ideal_residue_weight c.1.1 c.1.2 (auxiliaryScaledResidueWeight c p) f
  simpa only [auxiliaryScaledResidueWeight_mk,auxiliaryScaledTwistedComplete] using h

#print axioms auxiliaryPoisson_zero_coefficients
#print axioms poisson_auxiliary_masked_source
#print axioms poisson_auxiliary_scaled_source
end WaringSiegel.WSL3Poisson
