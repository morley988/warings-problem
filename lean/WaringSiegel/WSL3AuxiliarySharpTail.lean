import WaringSiegel.WSL3AuxiliaryGlobalMass
import WaringSiegel.WSL3AuxiliarySummability
import WaringSiegel.WSL3CubicAuxiliary173

/-! # WSL3: actual auxiliary cubic series, its uniform conductor moment and tail

The coefficients use the common modulus I ∩ (p), with units required only
modulo (p), and the literal p-scaled cubic sum. No Euler identity or
cancellation between characters is assumed in this convergence argument.
-/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliaryCubicCharacterContribution_five_quarters_uniform_bound
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal) :
    Summable (fun c : CubicConductorCharacter K =>
      (Ideal.absNorm c.1.1 : ℝ)^(5/4 : ℝ) *
        ‖auxiliaryCubicCharacterContribution c p hp ν‖) ∧
    (∑' c : CubicConductorCharacter K,
      (Ideal.absNorm c.1.1 : ℝ)^(5/4 : ℝ) *
        ‖auxiliaryCubicCharacterContribution c p hp ν‖) ≤
      cubicSharpUniformSingularSeriesConstant K *
        (Ideal.absNorm (Ideal.span ({p} : Set (𝓞 K))) : ℝ)^2 := by
  let P := Ideal.span ({p} : Set (𝓞 K))
  have hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
  apply auxiliary_weighted_summable_of_finite_mass_bound
  intro M hM hMP
  have hpv : ∀ v ∈ idealPrimeSupport P hP, p ∈ v.asIdeal := by
    intro v hv
    exact (Ideal.span_singleton_le_iff_mem v.asIdeal).mp
      (Ideal.dvd_iff_le.mp ((mem_idealPrimeSupport_iff_dvd P hP v).mp hv))
  exact finiteMaskedConductorMass_global_bound M P hM hP hMP p ν rfl
    (fun v hv => (hgood v (hpv v hv)).1)
    (fun v hv => (hgood v (hpv v hv)).2)

theorem auxiliaryCubicCharacterContribution_rational_prime_weighted_bound
    (p : ℕ) (hp : p.Prime) (hlarge : 173 ≤ p) (ν : 𝓞 K) :
    let hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
    Summable (fun c : CubicConductorCharacter K =>
      (Ideal.absNorm c.1.1 : ℝ)^(5/4 : ℝ) *
        ‖auxiliaryCubicCharacterContribution c (p : 𝓞 K) hp0 ν‖) ∧
    (∑' c : CubicConductorCharacter K,
      (Ideal.absNorm c.1.1 : ℝ)^(5/4 : ℝ) *
        ‖auxiliaryCubicCharacterContribution c (p : 𝓞 K) hp0 ν‖) ≤
      cubicSharpUniformSingularSeriesConstant K * (p : ℝ)^(2 * Module.finrank ℚ K) := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb := auxiliaryCubicCharacterContribution_five_quarters_uniform_bound
    (p : 𝓞 K) hp0 ν (fun v hpv =>
      ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hpv,
       hlarge.trans (rational_prime_le_residue_norm v hp hpv)⟩)
  simpa only [ideal_absNorm_span_nat, Nat.cast_pow, ← pow_mul, Nat.mul_comm] using hb

theorem auxiliaryCubicCharacterContribution_norm_summable
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal) :
    Summable (fun c : CubicConductorCharacter K =>
      ‖auxiliaryCubicCharacterContribution c p hp ν‖) := by
  obtain ⟨hs,-⟩ := auxiliaryCubicCharacterContribution_five_quarters_uniform_bound p hp ν hgood
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro c
  have hI : 1 ≤ (Ideal.absNorm c.1.1 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp c.1.2)
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_rpow hI (by norm_num : (0 : ℝ) ≤ 5/4))

def auxiliaryCubicSingularSeries (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) : ℂ :=
  ∑' c : CubicConductorCharacter K, auxiliaryCubicCharacterContribution c p hp ν

theorem auxiliaryCubicCharacterContribution_absolute_tail_five_quarters
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal)
    (Q : ℝ) (hQ : 0 < Q) :
    (∑' c : {c : CubicConductorCharacter K // Q < (Ideal.absNorm c.1.1 : ℝ)},
      ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖) ≤
      cubicSharpUniformSingularSeriesConstant K *
        (Ideal.absNorm (Ideal.span ({p} : Set (𝓞 K))) : ℝ)^2 / Q^(5/4 : ℝ) := by
  let S : Set (CubicConductorCharacter K) := {c | Q < (Ideal.absNorm c.1.1 : ℝ)}
  obtain ⟨hs,hb⟩ := auxiliaryCubicCharacterContribution_five_quarters_uniform_bound p hp ν hgood
  have hn := auxiliaryCubicCharacterContribution_norm_summable p hp ν hgood
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun c : S => ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖) at hns
  change Summable (fun c : S => (Ideal.absNorm c.1.1.1 : ℝ)^(5/4 : ℝ) *
    ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖) at hss
  have hsub := (Summable.tsum_subtype_le _ S (fun c => by positivity) hs).trans hb
  have hle (c : S) : Q^(5/4 : ℝ) * ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖ ≤
      (Ideal.absNorm c.1.1.1 : ℝ)^(5/4 : ℝ) *
        ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖ :=
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hQ.le c.2.le (by norm_num)) (norm_nonneg _)
  have hsum := (hns.mul_left (Q^(5/4 : ℝ))).tsum_le_tsum hle hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr
  simpa only [mul_comm] using hsum.trans hsub

end WaringSiegel
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_five_quarters_uniform_bound
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_rational_prime_weighted_bound
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_absolute_tail_five_quarters
