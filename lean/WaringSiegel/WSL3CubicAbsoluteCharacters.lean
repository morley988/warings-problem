import WaringSiegel.WSL3CubicSingularSeriesTail

/-! # WSL3: absolute convergence before grouping individual cubic characters -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexConjugate NumberField
namespace WaringSiegel

theorem finiteRingCubicSum_conj {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : conj (finiteRingPowerSum ψ 3) = finiteRingPowerSum ψ 3 := by
  have hterm (x : R) : conj (ψ (x^3)) = ψ ((-x)^3) := by
    rw [← AddChar.inv_apply_eq_conj, ← ψ.map_neg_eq_inv]
    congr 1
    ring
  simp only [finiteRingPowerSum, map_sum, hterm]
  exact (Equiv.neg R).bijective.sum_comp (fun x : R => ψ (x^3))

theorem complex_eighth_pow_eq_norm_of_conj_eq {z : ℂ} (hz : conj z = z) :
    z^8 = ((‖z‖^8 : ℝ) : ℂ) := by
  have h := Complex.mul_conj' z
  rw [hz, ← pow_two] at h
  rw [← Complex.ofReal_pow] at h
  calc
    z^8 = (z^2)^4 := by ring
    _ = (((‖z‖^2 : ℝ) : ℂ))^4 := congrArg (fun x : ℂ => x^4) h
    _ = _ := by push_cast; ring

theorem finiteRingCubicCharacterTerm_zero_eq_norm
    {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) (b : R) :
    finiteRingPowerCharacterTerm 3 8 (0 : R) ψ =
      (‖finiteRingPowerCharacterTerm 3 8 b ψ‖ : ℂ) := by
  let z : ℂ := finiteRingPowerSum ψ 3 / (Fintype.card R : ℂ)
  have hz : conj z = z := by
    simp only [z, map_div₀, finiteRingCubicSum_conj, map_natCast]
  have he := complex_eighth_pow_eq_norm_of_conj_eq hz
  simpa only [finiteRingPowerCharacterTerm, neg_zero, ψ.map_zero_eq_one,
    mul_one, norm_mul, norm_pow, ψ.norm_apply] using he

variable {K : Type*} [Field K] [NumberField K]

/-- At target zero the even power is nonnegative term by term. Its sum is
therefore the absolute character mass at every target. -/
theorem idealPrimitiveCubicCoefficient_zero_norm_eq_absolute_mass
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (ν : 𝓞 K) :
    letI := idealResidueFintype I hI
    (∑ ψ ∈ primitiveConductorCharacters I,
      ‖finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk I ν) ψ‖) =
        ‖idealPrimitiveCubicCoefficient I hI 0‖ := by
  letI := idealResidueFintype I hI
  have he : idealPrimitiveCubicCoefficient I hI 0 =
      ((∑ ψ ∈ primitiveConductorCharacters I,
        ‖finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk I ν) ψ‖ : ℝ) : ℂ) := by
    unfold idealPrimitiveCubicCoefficient
    rw [map_zero, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    exact finiteRingCubicCharacterTerm_zero_eq_norm ψ _
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]

def PrimitiveIdealCharacter (I : {I : Ideal (𝓞 K) // I ≠ 0}) :=
  {ψ : AddChar (𝓞 K ⧸ I.1) ℂ // quotientCharacterConductor I.1 ψ = I.1}

def primitiveIdealCharacterFintype (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    Fintype (PrimitiveIdealCharacter I) := by
  letI := idealResidueFintype I.1 I.2
  unfold PrimitiveIdealCharacter
  infer_instance

def CubicConductorCharacter (K : Type*) [Field K] [NumberField K] :=
  Σ I : {I : Ideal (𝓞 K) // I ≠ 0}, PrimitiveIdealCharacter I

def cubicCharacterContribution (c : CubicConductorCharacter K) (ν : 𝓞 K) : ℂ :=
  letI := idealResidueFintype c.1.1 c.1.2
  finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk c.1.1 ν) c.2.1

theorem cubicCharacterContribution_fiber_sum (I : {I : Ideal (𝓞 K) // I ≠ 0}) (ν : 𝓞 K) :
    (∑' ψ : PrimitiveIdealCharacter I, cubicCharacterContribution ⟨I,ψ⟩ ν) =
      idealPrimitiveCubicCoefficient I.1 I.2 ν := by
  letI := idealResidueFintype I.1 I.2
  letI := primitiveIdealCharacterFintype I
  simp only [tsum_fintype, cubicCharacterContribution, idealPrimitiveCubicCoefficient,
    PrimitiveIdealCharacter, primitiveConductorCharacters]
  exact (Finset.sum_subtype (p := fun ψ => quotientCharacterConductor I.1 ψ = I.1)
    (Finset.univ.filter (fun ψ => quotientCharacterConductor I.1 ψ = I.1))
    (by intro ψ; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun ψ => finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk I.1 ν) ψ)).symm

theorem cubicCharacterContribution_fiber_norm_sum (I : {I : Ideal (𝓞 K) // I ≠ 0}) (ν : 𝓞 K) :
    (∑' ψ : PrimitiveIdealCharacter I, ‖cubicCharacterContribution ⟨I,ψ⟩ ν‖) =
      ‖idealPrimitiveCubicCoefficient I.1 I.2 0‖ := by
  letI := idealResidueFintype I.1 I.2
  letI := primitiveIdealCharacterFintype I
  rw [← idealPrimitiveCubicCoefficient_zero_norm_eq_absolute_mass I.1 I.2 ν]
  simp only [tsum_fintype, cubicCharacterContribution, PrimitiveIdealCharacter,
    primitiveConductorCharacters]
  exact (Finset.sum_subtype (p := fun ψ => quotientCharacterConductor I.1 ψ = I.1)
    (Finset.univ.filter (fun ψ => quotientCharacterConductor I.1 ψ = I.1))
    (by intro ψ; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun ψ => ‖finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk I.1 ν) ψ‖)).symm

/-- This is absolute convergence over the individual exact-conductor
characters, before any grouping by conductor ideal. -/
theorem cubicCharacterContribution_norm_summable (ν : 𝓞 K) :
    Summable (fun c : CubicConductorCharacter K => ‖cubicCharacterContribution c ν‖) := by
  apply (summable_sigma_of_nonneg (fun c => norm_nonneg (cubicCharacterContribution c ν))).mpr
  constructor
  · intro I
    letI := primitiveIdealCharacterFintype I
    exact Summable.of_finite
  · simp only [cubicCharacterContribution_fiber_norm_sum]
    exact idealPrimitiveCubicCoefficient_norm_summable_all_targets 0

theorem cubicCharacterContribution_tsum (ν : 𝓞 K) :
    (∑' c : CubicConductorCharacter K, cubicCharacterContribution c ν) = cubicSingularSeries ν := by
  calc
    _ = ∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
        ∑' ψ : PrimitiveIdealCharacter I, cubicCharacterContribution ⟨I,ψ⟩ ν :=
      (cubicCharacterContribution_norm_summable ν).of_norm.tsum_sigma
    _ = _ := by simp only [cubicCharacterContribution_fiber_sum, cubicSingularSeries]

end WaringSiegel

#print axioms WaringSiegel.cubicCharacterContribution_norm_summable
#print axioms WaringSiegel.cubicCharacterContribution_tsum
