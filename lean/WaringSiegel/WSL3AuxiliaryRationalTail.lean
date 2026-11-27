import WaringSiegel.WSL3AuxiliarySharpTail
import WaringSiegel.WSL3AuxiliaryRationalCenters

/-! # WSL3: auxiliary convergence and tails over actual rational trace centers -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem rationalCenterAuxiliaryContribution_norm_summable
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal) :
    Summable (fun q : RationalTraceCenter K => ‖rationalCenterAuxiliaryContribution q p hp ν‖) :=
  (auxiliaryCubicCharacterContribution_norm_summable p hp ν hgood).comp_injective
    cubicConductorCharacterEquivRationalCenter.symm.injective

theorem rationalCenterAuxiliaryContribution_tsum
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    (∑' q : RationalTraceCenter K, rationalCenterAuxiliaryContribution q p hp ν) =
      auxiliaryCubicSingularSeries p hp ν := by
  exact cubicConductorCharacterEquivRationalCenter.symm.tsum_eq
    (fun c => auxiliaryCubicCharacterContribution c p hp ν)

theorem rationalCenterAuxiliaryContribution_five_quarters_uniform_bound
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal) :
    Summable (fun q : RationalTraceCenter K =>
      (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)^(5/4 : ℝ) *
        ‖rationalCenterAuxiliaryContribution q p hp ν‖) ∧
    (∑' q : RationalTraceCenter K,
      (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)^(5/4 : ℝ) *
        ‖rationalCenterAuxiliaryContribution q p hp ν‖) ≤
      cubicSharpUniformSingularSeriesConstant K *
        (Ideal.absNorm (Ideal.span ({p} : Set (𝓞 K))) : ℝ)^2 := by
  let e := cubicConductorCharacterEquivRationalCenter (K := K)
  have he (q : RationalTraceCenter K) :
      rationalTraceCenterConductor q = (e.symm q).1.1 := by
    have hc := cubicConductorCharacterToCenter_conductor (e.symm q)
    change rationalTraceCenterConductor (e (e.symm q)) = _ at hc
    simpa only [Equiv.apply_symm_apply] using hc
  obtain ⟨hs,hb⟩ := auxiliaryCubicCharacterContribution_five_quarters_uniform_bound p hp ν hgood
  constructor
  · simpa only [he,rationalCenterAuxiliaryContribution] using
      hs.comp_injective e.symm.injective
  · simpa only [he,rationalCenterAuxiliaryContribution] using
      (e.symm.tsum_eq (fun c => (Ideal.absNorm c.1.1 : ℝ)^(5/4 : ℝ) *
        ‖auxiliaryCubicCharacterContribution c p hp ν‖)).trans_le hb

theorem rationalCenterAuxiliaryContribution_absolute_tail_five_quarters
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal)
    (Q : ℝ) (hQ : 0 < Q) :
    (∑' q : {q : RationalTraceCenter K //
      Q < (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)},
      ‖rationalCenterAuxiliaryContribution q.1 p hp ν‖) ≤
      cubicSharpUniformSingularSeriesConstant K *
        (Ideal.absNorm (Ideal.span ({p} : Set (𝓞 K))) : ℝ)^2 / Q^(5/4 : ℝ) := by
  let S : Set (RationalTraceCenter K) :=
    {q | Q < (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)}
  obtain ⟨hs,hb⟩ := rationalCenterAuxiliaryContribution_five_quarters_uniform_bound p hp ν hgood
  have hn := rationalCenterAuxiliaryContribution_norm_summable p hp ν hgood
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun q : S => ‖rationalCenterAuxiliaryContribution q.1 p hp ν‖) at hns
  change Summable (fun q : S =>
    (Ideal.absNorm (rationalTraceCenterConductor q.1) : ℝ)^(5/4 : ℝ) *
      ‖rationalCenterAuxiliaryContribution q.1 p hp ν‖) at hss
  have hsub := (Summable.tsum_subtype_le _ S (fun q => by positivity) hs).trans hb
  have hle (q : S) : Q^(5/4 : ℝ) * ‖rationalCenterAuxiliaryContribution q.1 p hp ν‖ ≤
      (Ideal.absNorm (rationalTraceCenterConductor q.1) : ℝ)^(5/4 : ℝ) *
        ‖rationalCenterAuxiliaryContribution q.1 p hp ν‖ :=
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hQ.le q.2.le (by norm_num)) (norm_nonneg _)
  have hsum := (hns.mul_left (Q^(5/4 : ℝ))).tsum_le_tsum hle hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr
  simpa only [mul_comm] using hsum.trans hsub

theorem rationalCenterAuxiliaryContribution_rational_prime_tail
    (p : ℕ) (hp : p.Prime) (hlarge : 173 ≤ p) (ν : 𝓞 K)
    (Q : ℝ) (hQ : 0 < Q) :
    let hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
    (∑' q : {q : RationalTraceCenter K //
      Q < (Ideal.absNorm (rationalTraceCenterConductor q) : ℝ)},
      ‖rationalCenterAuxiliaryContribution q.1 (p : 𝓞 K) hp0 ν‖) ≤
      cubicSharpUniformSingularSeriesConstant K *
        (p : ℝ)^(2 * Module.finrank ℚ K) / Q^(5/4 : ℝ) := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb := rationalCenterAuxiliaryContribution_absolute_tail_five_quarters
    (p : 𝓞 K) hp0 ν (fun v hpv =>
      ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hpv,
       hlarge.trans (rational_prime_le_residue_norm v hp hpv)⟩) Q hQ
  simpa only [ideal_absNorm_span_nat, Nat.cast_pow, ← pow_mul, Nat.mul_comm] using hb

end WaringSiegel
#print axioms WaringSiegel.rationalCenterAuxiliaryContribution_five_quarters_uniform_bound
#print axioms WaringSiegel.rationalCenterAuxiliaryContribution_rational_prime_tail
