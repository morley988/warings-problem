import WaringSiegel.WSL4WeilIdealCRT
import WaringSiegel.WSL3IdealPoissonCenter

/-! # The actual arbitrary-twist complete coefficient in ideal Poisson

This removes the finite exponential-sum premise from the cubic major-arc
interfaces.  The leading character has exact trace conductor; every frequency
in the actual trace-dual ideal gives a genuine linear quotient character.
-/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical NumberField nonZeroDivisors
open NumberField WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem ideal_le_traceConductor_of_dual_mem
    (I : Ideal (𝓞 K)) (hI : I≠0) {ξ : K}
    (hξ : ξ ∈ inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    I≤traceConductor ξ := by
  have hIF : (I : FractionalIdeal (𝓞 K)⁰ K)≠0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  intro a ha
  change (a:K)*ξ∈inverseDifferent K
  have hm := FractionalIdeal.mul_mem_mul hξ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ ha)
  have he : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹)*
      (I : FractionalIdeal (𝓞 K)⁰ K)=inverseDifferent K := by
    rw [mul_assoc,inv_mul_cancel₀ hIF,mul_one]
  rw [he] at hm
  simpa only [mul_comm,← RingOfIntegers.coe_eq_algebraMap] using hm

def idealDualResidueChar (I : Ideal (𝓞 K)) (hI : I≠0)
    (ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) :
    AddChar (𝓞 K ⧸ I) ℂ :=
  traceIdealAddChar I ⟨traceRationalPoint (ξ:K),(ξ:K),rfl,
    ideal_le_traceConductor_of_dual_mem I hI ξ.property⟩

@[simp] theorem idealDualResidueChar_mk (I : Ideal (𝓞 K)) (hI : I≠0)
    (ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) (x : 𝓞 K) :
    idealDualResidueChar I hI ξ (Ideal.Quotient.mk I x)=
      archimedeanTraceCharacter (mixedEmbedding K (ξ:K)) (mixedEmbedding K (x:K)) := by
  rw [idealDualResidueChar,traceIdealAddChar_mk]
  change traceTorusCharacter x (traceRationalPoint (ξ:K))=_
  rw [traceRationalPoint,traceTorusCharacter_mk]
  unfold archimedeanTraceCharacter
  rw [mul_comm (mixedEmbedding K (x:K)) (mixedEmbedding K (ξ:K))]

theorem fieldCenterResidueChar_isPrimitive (γ : K) : (fieldCenterResidueChar γ).IsPrimitive := by
  apply (quotient_character_primitive_iff_exact_conductor _ _).mpr
  apply quotientCharacterConductor_eq_traceConductor (traceConductor γ) (fieldCenterResidueChar γ) γ
  intro x
  rfl

theorem fieldCenterCompleteSum_eq_idealTwistedCubicSum (γ : K)
    (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) :
    fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))=
      idealTwistedCubicSum (traceConductor γ) (traceConductor_ne_zero γ)
        (fieldCenterResidueChar γ) (idealDualResidueChar _ (traceConductor_ne_zero γ) ξ) := by
  letI := fieldCenterResidueFintype γ
  unfold fieldCenterCompleteSum idealCompleteTraceFactor idealTwistedCubicSum twistedPowerSum
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  simpa only [idealResidueRepresentative_spec] using
    (idealDualResidueChar_mk (traceConductor γ) (traceConductor_ne_zero γ) ξ
      (idealResidueRepresentative (traceConductor γ) q)).symm

/-- The complete coefficient required by cubic ideal Poisson, with no
unproved finite-field, prime-power, or arbitrary-twist bound as a premise. -/
theorem fieldCenterCompleteSum_cubic_kappa_bound (γ : K)
    (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) :
    ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖≤
      ((traceConductor γ).absNorm:ℝ)*
        cubicKappa cubicTwistExceptionalConstant ⟨traceConductor γ,traceConductor_ne_zero γ⟩ := by
  rw [fieldCenterCompleteSum_eq_idealTwistedCubicSum]
  exact idealTwistedCubicSum_kappa_bound _ _ _ _ (fieldCenterResidueChar_isPrimitive γ)
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.fieldCenterCompleteSum_cubic_kappa_bound
