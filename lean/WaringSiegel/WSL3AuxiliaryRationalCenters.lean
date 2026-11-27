import WaringSiegel.WSL3AuxiliaryInflation

/-! # WSL3: the literal auxiliary summand at an actual rational trace center -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def rationalCenterAuxiliaryContribution (q : RationalTraceCenter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) : ℂ :=
  auxiliaryCubicCharacterContribution (cubicConductorCharacterEquivRationalCenter.symm q) p hp ν

theorem rationalCenterAuxiliaryContribution_formula
    (q : RationalTraceCenter K) (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    let I := rationalTraceCenterConductor q
    let M := auxiliaryCommonModulus I p
    letI := idealResidueFintype I (rationalTraceCenterConductor_ne_zero q)
    letI := idealResidueFintype M
      (auxiliaryCommonModulus_ne_zero I (rationalTraceCenterConductor_ne_zero q) p hp)
    let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ I) := Ideal.Quotient.factor inf_le_left
    let g : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ Ideal.span ({p} : Set (𝓞 K))) :=
      Ideal.Quotient.factor inf_le_right
    rationalCenterAuxiliaryContribution q p hp ν =
      (finiteMaskedPowerSum g
        ((rationalTraceCenterQuotientCharacter q).compAddMonoidHom f.toAddMonoidHom) 3 /
          (Ideal.absNorm M : ℂ))^4 *
      (finiteRingScaledPowerSum (rationalTraceCenterQuotientCharacter q) 3
        (Ideal.Quotient.mk I p) / (Ideal.absNorm I : ℂ))^4 *
      traceTorusCharacter (-ν) q.1 := by
  let I := rationalTraceCenterConductor q
  let M := auxiliaryCommonModulus I p
  letI := idealResidueFintype I (rationalTraceCenterConductor_ne_zero q)
  letI := idealResidueFintype M
    (auxiliaryCommonModulus_ne_zero I (rationalTraceCenterConductor_ne_zero q) p hp)
  let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ I) := Ideal.Quotient.factor inf_le_left
  let g : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ Ideal.span ({p} : Set (𝓞 K))) :=
    Ideal.Quotient.factor inf_le_right
  have hcI : Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  have hcM : Fintype.card (𝓞 K ⧸ M) = Ideal.absNorm M := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  unfold rationalCenterAuxiliaryContribution
  rw [← rationalTraceCenterPrimitiveIndex_eq_inverse]
  change (finiteMaskedPowerSum g
      ((rationalTraceCenterQuotientCharacter q).compAddMonoidHom f.toAddMonoidHom) 3 /
        (Fintype.card (𝓞 K ⧸ M) : ℂ))^4 *
    (finiteRingScaledPowerSum (rationalTraceCenterQuotientCharacter q) 3
      (Ideal.Quotient.mk I p) / (Fintype.card (𝓞 K ⧸ I) : ℂ))^4 *
    rationalTraceCenterQuotientCharacter q (-Ideal.Quotient.mk I ν) = _
  rw [hcI, hcM, ← (Ideal.Quotient.mk I).map_neg ν]
  rfl

end WaringSiegel
#print axioms WaringSiegel.rationalCenterAuxiliaryContribution_formula
