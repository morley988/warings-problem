import WaringSiegel.WSL4MajorSources
import WaringSiegel.WSL4PowerCharacters
import WaringSiegel.WSL2TraceMajorArcUnion

/-! # The Poisson main coefficient is the actual conductor-series term -/
noncomputable section
set_option maxHeartbeats 1000000
open NumberField NumberField.mixedEmbedding WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def fieldRationalCenter (γ : K) : RationalTraceCenter K :=
  ⟨traceRationalPoint γ,γ,rfl⟩

theorem fieldRationalCenter_conductor (γ : K) :
    rationalTraceCenterConductor (fieldRationalCenter γ) = traceConductor γ :=
  traceFrequencyAddChar_idealConductor γ

def fieldPowerCharacter (γ : K) : PowerConductorCharacter K :=
  ⟨⟨traceConductor γ,traceConductor_ne_zero γ⟩,
    ⟨fieldCenterResidueChar γ,by
      rw [fieldCenterResidueChar,traceIdealAddChar_conductor]
      exact traceFrequencyAddChar_idealConductor γ⟩⟩

theorem fieldPowerCharacter_center (γ : K) :
    cubicConductorCharacterEquivRationalCenter (fieldPowerCharacter γ) = fieldRationalCenter γ := by
  apply Subtype.ext
  change ((traceIdealCharacterEquiv (traceConductor γ) (traceConductor_ne_zero γ)).symm
    ((traceIdealCharacterEquiv (traceConductor γ) (traceConductor_ne_zero γ))
      ⟨traceRationalPoint γ,γ,rfl,le_rfl⟩)).1 = traceRationalPoint γ
  rw [Equiv.symm_apply_apply]

theorem majorCompleteCoefficient_eq_character (k n : ℕ) (target : 𝓞 K) (γ : K) :
    majorCompleteCoefficient k n target γ =
      powerCharacterContribution k n (fieldPowerCharacter γ) target := by
  letI := fieldCenterResidueFintype γ
  have hc : Fintype.card (𝓞 K ⧸ traceConductor γ) = (traceConductor γ).absNorm := by
    rw [← Nat.card_eq_fintype_card,Ideal.absNorm_apply]
    rfl
  have hphase : fieldCenterResidueChar γ (-Ideal.Quotient.mk (traceConductor γ) target) =
      traceTorusCharacter (-target) (traceRationalPoint γ) := by
    rw [← (Ideal.Quotient.mk (traceConductor γ)).map_neg target]
    rfl
  change majorCompleteCoefficient k n target γ =
    finiteRingPowerCharacterTerm k n (Ideal.Quotient.mk (traceConductor γ) target)
      (fieldCenterResidueChar γ)
  rw [majorCompleteCoefficient,fieldCenterCompleteSum_zero]
  simp only [finiteRingPowerCharacterTerm,finiteRingPowerSum,hc,hphase,div_eq_mul_inv,
    mul_comm]

theorem majorCompleteCoefficient_eq_rational (k n : ℕ) (target : 𝓞 K) (γ : K) :
    majorCompleteCoefficient k n target γ =
      rationalCenterPowerContribution k n (fieldRationalCenter γ) target := by
  rw [rationalCenterPowerContribution,← fieldPowerCharacter_center γ,
    Equiv.symm_apply_apply]
  exact majorCompleteCoefficient_eq_character k n target γ

def boundedCenterAsRational {N : ℕ} (q : traceRationalCenters K N) : RationalTraceCenter K :=
  ⟨q.1,traceCenterRepresentative q,(traceCenterRepresentative_spec q).1⟩

theorem fieldRationalCenter_representative {N : ℕ} (q : traceRationalCenters K N) :
    fieldRationalCenter (traceCenterRepresentative q) = boundedCenterAsRational q :=
  Subtype.ext (traceCenterRepresentative_spec q).1

theorem boundedCenterAsRational_conductor {N : ℕ} (q : traceRationalCenters K N) :
    rationalTraceCenterConductor (boundedCenterAsRational q) =
      traceConductor (traceCenterRepresentative q) := by
  rw [← fieldRationalCenter_representative,fieldRationalCenter_conductor]

theorem boundedCenterAsRational_injective (N : ℕ) :
    Function.Injective (boundedCenterAsRational (K := K) (N := N)) := by
  intro q r h
  exact Subtype.ext (congrArg (fun q : RationalTraceCenter K => q.1) h)

local instance characterCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

def rationalCentersUpTo (N : ℕ) : Finset (RationalTraceCenter K) :=
  Finset.univ.map ⟨boundedCenterAsRational,boundedCenterAsRational_injective N⟩

theorem mem_rationalCentersUpTo (N : ℕ) (q : RationalTraceCenter K) :
    q ∈ rationalCentersUpTo N ↔ (rationalTraceCenterConductor q).absNorm≤N := by
  constructor
  · intro h
    obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp h
    change (rationalTraceCenterConductor (boundedCenterAsRational r)).absNorm≤N
    rw [boundedCenterAsRational_conductor]
    exact (traceCenterRepresentative_spec r).2
  · intro h
    obtain ⟨γ,hγ⟩ := q.2
    have hcond : rationalTraceCenterConductor q=traceConductor γ := by
      unfold rationalTraceCenterConductor
      rw [← hγ,traceFrequencyAddChar_idealConductor]
    let r : traceRationalCenters K N := ⟨q.1,γ,hγ,by rwa [← hcond]⟩
    exact Finset.mem_map.mpr ⟨r,Finset.mem_univ _,Subtype.ext rfl⟩

theorem finite_majorCompleteCoefficient_sum_eq (k n N : ℕ) (target : 𝓞 K) :
    (∑ q : traceRationalCenters K N,majorCompleteCoefficient k n target (traceCenterRepresentative q)) =
      ∑ q ∈ rationalCentersUpTo N,rationalCenterPowerContribution k n q target := by
  simp only [rationalCentersUpTo,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro q hq
  rw [majorCompleteCoefficient_eq_rational,fieldRationalCenter_representative]
  rfl

#print axioms majorCompleteCoefficient_eq_rational
#print axioms mem_rationalCentersUpTo
#print axioms finite_majorCompleteCoefficient_sum_eq
end WaringSiegel.WSL4
