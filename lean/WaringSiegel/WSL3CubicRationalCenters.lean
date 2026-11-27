import WaringSiegel.WSL3CubicSharpTail

/-! # WSL3: individual exact-conductor characters are the actual rational trace centers -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def RationalTraceCenter (K : Type*) [Field K] [NumberField K] :=
  {q : ArchimedeanTraceTorus K // ∃ γ : K, traceRationalPoint γ = q}

def rationalTraceCenterConductor (q : RationalTraceCenter K) : Ideal (𝓞 K) :=
  addCharIdealConductor (traceFrequencyAddChar q.1)

theorem rationalTraceCenterConductor_ne_zero (q : RationalTraceCenter K) :
    rationalTraceCenterConductor q ≠ 0 := by
  obtain ⟨γ,hγ⟩ := q.2
  unfold rationalTraceCenterConductor
  rw [← hγ, traceFrequencyAddChar_idealConductor]
  exact traceConductor_ne_zero γ

theorem traceIdealAddChar_conductor (I : Ideal (𝓞 K)) (q : traceIdealCenters I) :
    quotientCharacterConductor I (traceIdealAddChar I q) =
      addCharIdealConductor (traceFrequencyAddChar q.1) := rfl

def cubicConductorCharacterToCenter (c : CubicConductorCharacter K) : RationalTraceCenter K := by
  let q := (traceIdealCharacterEquiv c.1.1 c.1.2).symm c.2.1
  exact ⟨q.1, by obtain ⟨γ,hγ,-⟩ := q.2; exact ⟨γ,hγ⟩⟩

theorem cubicConductorCharacterToCenter_conductor (c : CubicConductorCharacter K) :
    rationalTraceCenterConductor (cubicConductorCharacterToCenter c) = c.1.1 := by
  let q := (traceIdealCharacterEquiv c.1.1 c.1.2).symm c.2.1
  have he : traceIdealAddChar c.1.1 q = c.2.1 :=
    (traceIdealCharacterEquiv c.1.1 c.1.2).apply_symm_apply _
  change addCharIdealConductor (traceFrequencyAddChar q.1) = _
  rw [← traceIdealAddChar_conductor c.1.1 q, he]
  exact c.2.2

theorem cubicConductorCharacterToCenter_injective :
    Function.Injective (cubicConductorCharacterToCenter (K := K)) := by
  rintro ⟨I,ψ⟩ ⟨J,φ⟩ h
  have hI : I = J := Subtype.ext (by
    have he := congrArg rationalTraceCenterConductor h
    simpa only [cubicConductorCharacterToCenter_conductor] using he)
  subst J
  have hq : (traceIdealCharacterEquiv I.1 I.2).symm ψ.1 =
      (traceIdealCharacterEquiv I.1 I.2).symm φ.1 := by
    apply Subtype.ext
    exact congrArg (fun q : RationalTraceCenter K => q.1) h
  have hψ : ψ = φ := Subtype.ext ((traceIdealCharacterEquiv I.1 I.2).symm.injective hq)
  cases hψ
  rfl

theorem cubicConductorCharacterToCenter_surjective :
    Function.Surjective (cubicConductorCharacterToCenter (K := K)) := by
  intro q
  let I : {I : Ideal (𝓞 K) // I ≠ 0} :=
    ⟨rationalTraceCenterConductor q, rationalTraceCenterConductor_ne_zero q⟩
  have hqI : q.1 ∈ traceIdealCenters I.1 := by
    obtain ⟨γ,hγ⟩ := q.2
    refine ⟨γ,hγ,?_⟩
    change addCharIdealConductor (traceFrequencyAddChar q.1) ≤ traceConductor γ
    rw [← hγ, traceFrequencyAddChar_idealConductor]
  let qI : traceIdealCenters I.1 := ⟨q.1,hqI⟩
  let ψ : PrimitiveIdealCharacter I := ⟨traceIdealAddChar I.1 qI,
    by rw [traceIdealAddChar_conductor]; rfl⟩
  refine ⟨⟨I,ψ⟩, ?_⟩
  apply Subtype.ext
  change ((traceIdealCharacterEquiv I.1 I.2).symm
    ((traceIdealCharacterEquiv I.1 I.2) qI)).1 = q.1
  rw [Equiv.symm_apply_apply]

def cubicConductorCharacterEquivRationalCenter :
    CubicConductorCharacter K ≃ RationalTraceCenter K :=
  Equiv.ofBijective cubicConductorCharacterToCenter
    ⟨cubicConductorCharacterToCenter_injective, cubicConductorCharacterToCenter_surjective⟩

/-- The pure complete-sum term attached to a rational trace center, with its
actual conductor ideal and quotient character. -/
def rationalCenterCubicContribution (q : RationalTraceCenter K) (ν : 𝓞 K) : ℂ :=
  cubicCharacterContribution (cubicConductorCharacterEquivRationalCenter.symm q) ν

theorem rationalCenterCubicContribution_norm_summable (ν : 𝓞 K) :
    Summable (fun q : RationalTraceCenter K => ‖rationalCenterCubicContribution q ν‖) :=
  (cubicCharacterContribution_norm_summable ν).comp_injective
    cubicConductorCharacterEquivRationalCenter.symm.injective

theorem rationalCenterCubicContribution_tsum (ν : 𝓞 K) :
    (∑' q : RationalTraceCenter K, rationalCenterCubicContribution q ν) = cubicSingularSeries ν := by
  exact (cubicConductorCharacterEquivRationalCenter.symm.tsum_eq
    (fun c => cubicCharacterContribution c ν)).trans (cubicCharacterContribution_tsum ν)

theorem rationalCenterCubicContribution_five_quarters_uniform_bound (ν : 𝓞 K) :
    Summable (fun q : RationalTraceCenter K =>
      (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)^(5/4 : ℝ) *
        ‖rationalCenterCubicContribution q ν‖) ∧
    (∑' q : RationalTraceCenter K,
      (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)^(5/4 : ℝ) *
        ‖rationalCenterCubicContribution q ν‖) ≤ cubicSharpUniformSingularSeriesConstant K := by
  let e := cubicConductorCharacterEquivRationalCenter (K := K)
  have he (q : RationalTraceCenter K) :
      rationalTraceCenterConductor q = (e.symm q).1.1 := by
    have hc := cubicConductorCharacterToCenter_conductor (e.symm q)
    change rationalTraceCenterConductor (e (e.symm q)) = _ at hc
    simpa only [Equiv.apply_symm_apply] using hc
  obtain ⟨hs,hb⟩ := cubicCharacterContribution_five_quarters_uniform_bound ν
  constructor
  · simpa only [he, rationalCenterCubicContribution, cubicCharacterConductorNorm] using
      hs.comp_injective e.symm.injective
  · simpa only [he, rationalCenterCubicContribution, cubicCharacterConductorNorm] using
      (e.symm.tsum_eq (fun c => (cubicCharacterConductorNorm c : ℝ)^(5/4 : ℝ) *
        ‖cubicCharacterContribution c ν‖)).trans_le hb

end WaringSiegel
#print axioms WaringSiegel.cubicConductorCharacterEquivRationalCenter
#print axioms WaringSiegel.rationalCenterCubicContribution_five_quarters_uniform_bound
