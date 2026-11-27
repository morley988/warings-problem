import WaringSiegel.WSL3CubicRationalCenters

/-! # WSL3: the rational-center summand is the literal trace complete sum -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def rationalTraceCenterAsIdealCenter (q : RationalTraceCenter K) :
    traceIdealCenters (rationalTraceCenterConductor q) := by
  refine ⟨q.1, ?_⟩
  obtain ⟨γ,hγ⟩ := q.2
  refine ⟨γ,hγ,?_⟩
  unfold rationalTraceCenterConductor
  rw [← hγ, traceFrequencyAddChar_idealConductor]

def rationalTraceCenterQuotientCharacter (q : RationalTraceCenter K) :
    AddChar (𝓞 K ⧸ rationalTraceCenterConductor q) ℂ :=
  traceIdealAddChar _ (rationalTraceCenterAsIdealCenter q)

theorem rationalTraceCenterQuotientCharacter_conductor (q : RationalTraceCenter K) :
    quotientCharacterConductor (rationalTraceCenterConductor q)
      (rationalTraceCenterQuotientCharacter q) = rationalTraceCenterConductor q := by
  rw [rationalTraceCenterQuotientCharacter, traceIdealAddChar_conductor]
  rfl

def rationalTraceCenterPrimitiveIndex (q : RationalTraceCenter K) : CubicConductorCharacter K :=
  ⟨⟨rationalTraceCenterConductor q, rationalTraceCenterConductor_ne_zero q⟩,
    ⟨rationalTraceCenterQuotientCharacter q, rationalTraceCenterQuotientCharacter_conductor q⟩⟩

theorem rationalTraceCenterPrimitiveIndex_eq_inverse (q : RationalTraceCenter K) :
    rationalTraceCenterPrimitiveIndex q = cubicConductorCharacterEquivRationalCenter.symm q := by
  apply cubicConductorCharacterEquivRationalCenter.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change ((traceIdealCharacterEquiv (rationalTraceCenterConductor q)
    (rationalTraceCenterConductor_ne_zero q)).symm
      ((traceIdealCharacterEquiv (rationalTraceCenterConductor q)
        (rationalTraceCenterConductor_ne_zero q)) (rationalTraceCenterAsIdealCenter q))).1 = q.1
  rw [Equiv.symm_apply_apply]
  rfl

/-- No auxiliary index remains in this formula: the sum is over the actual
conductor quotient, and the target factor is the actual trace-torus character. -/
theorem rationalCenterCubicContribution_formula (q : RationalTraceCenter K) (ν : 𝓞 K) :
    letI := idealResidueFintype (rationalTraceCenterConductor q) (rationalTraceCenterConductor_ne_zero q)
    rationalCenterCubicContribution q ν =
      ((∑ x : 𝓞 K ⧸ rationalTraceCenterConductor q,
          rationalTraceCenterQuotientCharacter q (x^3)) /
        (Ideal.absNorm (rationalTraceCenterConductor q) : ℂ))^8 *
          traceTorusCharacter (-ν) q.1 := by
  letI := idealResidueFintype (rationalTraceCenterConductor q) (rationalTraceCenterConductor_ne_zero q)
  have hc : Fintype.card (𝓞 K ⧸ rationalTraceCenterConductor q) =
      Ideal.absNorm (rationalTraceCenterConductor q) := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  unfold rationalCenterCubicContribution
  rw [← rationalTraceCenterPrimitiveIndex_eq_inverse]
  change finiteRingPowerCharacterTerm 3 8
      (Ideal.Quotient.mk (rationalTraceCenterConductor q) ν)
      (rationalTraceCenterQuotientCharacter q) = _
  unfold finiteRingPowerCharacterTerm finiteRingPowerSum
  rw [hc, ← (Ideal.Quotient.mk (rationalTraceCenterConductor q)).map_neg ν]
  rfl

end WaringSiegel
#print axioms WaringSiegel.rationalCenterCubicContribution_formula
