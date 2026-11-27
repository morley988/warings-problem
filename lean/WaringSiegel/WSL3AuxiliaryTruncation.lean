import WaringSiegel.WSL3AuxiliaryRationalTail

/-! # WSL3: finite rational-center truncations of the actual auxiliary series -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def cubicCharacterConductorCutoff (Q : ℕ) : Finset (CubicConductorCharacter K) :=
  (cubicConductorCutoff (K := K) Q).sigma
    (fun I => @Finset.univ (PrimitiveIdealCharacter I) (primitiveIdealCharacterFintype I))

@[simp] theorem mem_cubicCharacterConductorCutoff (Q : ℕ) (c : CubicConductorCharacter K) :
    c ∈ cubicCharacterConductorCutoff Q ↔ Ideal.absNorm c.1.1 ≤ Q := by
  letI := primitiveIdealCharacterFintype c.1
  unfold cubicCharacterConductorCutoff
  constructor
  · intro h
    exact (mem_cubicConductorCutoff Q c.1).mp (Finset.mem_sigma.mp h).1
  · intro h
    exact Finset.mem_sigma.mpr ⟨(mem_cubicConductorCutoff Q c.1).mpr h, Finset.mem_univ _⟩

def rationalTraceCenterCutoff (Q : ℕ) : Finset (RationalTraceCenter K) :=
  (cubicCharacterConductorCutoff Q).map cubicConductorCharacterEquivRationalCenter.toEmbedding

@[simp] theorem mem_rationalTraceCenterCutoff (Q : ℕ) (q : RationalTraceCenter K) :
    q ∈ rationalTraceCenterCutoff Q ↔
      Ideal.absNorm (rationalTraceCenterConductor q) ≤ Q := by
  let e := cubicConductorCharacterEquivRationalCenter (K := K)
  have hc := cubicConductorCharacterToCenter_conductor (e.symm q)
  change rationalTraceCenterConductor (e (e.symm q)) = _ at hc
  simp only [Equiv.apply_symm_apply] at hc
  change q ∈ (cubicCharacterConductorCutoff Q).map e.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, mem_cubicCharacterConductorCutoff, hc]

def auxiliaryCubicSingularSeriesTruncation (Q : ℕ)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) : ℂ :=
  ∑ c ∈ cubicCharacterConductorCutoff Q, auxiliaryCubicCharacterContribution c p hp ν

def rationalCenterAuxiliaryTruncation (Q : ℕ)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) : ℂ :=
  ∑ q ∈ rationalTraceCenterCutoff Q, rationalCenterAuxiliaryContribution q p hp ν

theorem rationalCenterAuxiliaryTruncation_eq (Q : ℕ)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    rationalCenterAuxiliaryTruncation Q p hp ν =
      auxiliaryCubicSingularSeriesTruncation Q p hp ν := by
  simp only [rationalCenterAuxiliaryTruncation, rationalTraceCenterCutoff, Finset.sum_map,
    Equiv.toEmbedding_apply, rationalCenterAuxiliaryContribution, Equiv.symm_apply_apply,
    auxiliaryCubicSingularSeriesTruncation]

theorem auxiliaryCubicSingularSeries_truncation_error
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal)
    (Q : ℕ) (hQ : 0 < Q) :
    ‖auxiliaryCubicSingularSeries p hp ν - auxiliaryCubicSingularSeriesTruncation Q p hp ν‖ ≤
      cubicSharpUniformSingularSeriesConstant K *
        (Ideal.absNorm (Ideal.span ({p} : Set (𝓞 K))) : ℝ)^2 / (Q : ℝ)^(5/4 : ℝ) := by
  have hn := auxiliaryCubicCharacterContribution_norm_summable p hp ν hgood
  have he := hn.of_norm.sum_add_tsum_subtype_compl (cubicCharacterConductorCutoff (K := K) Q)
  have htail : auxiliaryCubicSingularSeries p hp ν -
      auxiliaryCubicSingularSeriesTruncation Q p hp ν =
      ∑' c : {c : CubicConductorCharacter K // c ∉ cubicCharacterConductorCutoff Q},
        auxiliaryCubicCharacterContribution c.1 p hp ν := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)
  rw [htail]
  have hbound := norm_tsum_le_tsum_norm
    (hn.subtype {c | c ∉ cubicCharacterConductorCutoff Q})
  apply hbound.trans
  let e : {c : CubicConductorCharacter K // c ∉ cubicCharacterConductorCutoff Q} ≃
      {c : CubicConductorCharacter K // (Q : ℝ) < (Ideal.absNorm c.1.1 : ℝ)} :=
    Equiv.subtypeEquivRight (fun c => by
      rw [mem_cubicCharacterConductorCutoff, not_le]
      exact Nat.cast_lt.symm)
  have he' := e.tsum_eq (fun c => ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖)
  exact he'.trans_le
    (auxiliaryCubicCharacterContribution_absolute_tail_five_quarters p hp ν hgood
      (Q : ℝ) (by exact_mod_cast hQ))

theorem rationalCenterAuxiliaryTruncation_rational_prime_error
    (p : ℕ) (hp : p.Prime) (hlarge : 173 ≤ p) (ν : 𝓞 K)
    (Q : ℕ) (hQ : 0 < Q) :
    let hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
    ‖(∑' q : RationalTraceCenter K, rationalCenterAuxiliaryContribution q (p : 𝓞 K) hp0 ν) -
      rationalCenterAuxiliaryTruncation Q (p : 𝓞 K) hp0 ν‖ ≤
      cubicSharpUniformSingularSeriesConstant K *
        (p : ℝ)^(2 * Module.finrank ℚ K) / (Q : ℝ)^(5/4 : ℝ) := by
  dsimp only
  rw [rationalCenterAuxiliaryContribution_tsum, rationalCenterAuxiliaryTruncation_eq]
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb := auxiliaryCubicSingularSeries_truncation_error
    (p : 𝓞 K) hp0 ν (fun v hpv =>
      ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hpv,
       hlarge.trans (rational_prime_le_residue_norm v hp hpv)⟩) Q hQ
  simpa only [ideal_absNorm_span_nat, Nat.cast_pow, ← pow_mul, Nat.mul_comm] using hb

end WaringSiegel
#print axioms WaringSiegel.rationalCenterAuxiliaryTruncation_rational_prime_error
