import WaringSiegel.WSL3AuxiliaryEulerIdentity

/-! # Uniform positivity of the literal auxiliary cubic singular series -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem idealPrimeSupport_span_nat_eq_auxiliaryPrimeSet (p : ℕ) (hp : p.Prime) :
    let hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
    let P := Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
    let hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp0
    idealPrimeSupport P hP = cubicAuxiliaryPrimeSet (K := K) p hp := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  ext v
  rw [mem_idealPrimeSupport_iff_dvd, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem, mem_cubicAuxiliaryPrimeSet hp v]

/-- The positive constant is chosen before both the eligible nonzero target
and the rational auxiliary prime. The series here is the actual sum of the
masked/scaled complete-character coefficients from the ideal Poisson formula. -/
theorem auxiliaryCubicSingularSeries_uniform_positive_173 :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∀ (p : ℕ) (hp : p.Prime), 173 ≤ p →
        let hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
        Summable (fun a : CubicConductorCharacter K =>
          ‖auxiliaryCubicCharacterContribution a (p : 𝓞 K) hp0 ν‖) ∧
        (auxiliaryCubicSingularSeries (p : 𝓞 K) hp0 ν).im = 0 ∧
        c ≤ (auxiliaryCubicSingularSeries (p : 𝓞 K) hp0 ν).re := by
  obtain ⟨c,hc,hfamily⟩ :=
    modified_cubic_euler_product_uniform_positive_of_card_le_173 (K := K) (Module.finrank ℚ K)
  refine ⟨c,hc,?_⟩
  intro ν hν hν0 p hp hlarge
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨σ,hσ,hreplace⟩ := hfamily ν hν hν0
  have hm : Multipliable σ := by
    have hh := (hreplace ∅ (by simp) (by simp)).1
    simpa only [Finset.notMem_empty, if_false] using hh
  let S := cubicAuxiliaryPrimeSet (K := K) p hp
  have hS : ∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal := by
    intro v hv
    have hpv := (mem_cubicAuxiliaryPrimeSet hp v).mp hv
    exact ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hpv,
      hlarge.trans (rational_prime_le_residue_norm v hp hpv)⟩
  have hcard : S.card ≤ Module.finrank ℚ K :=
    prime_ideals_above_rational_prime_card_le hp S
      (fun v hv => (mem_cubicAuxiliaryPrimeSet hp v).mp hv)
  obtain ⟨-,hlower⟩ := hreplace S hcard hS
  have hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (p : 𝓞 K) ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal := by
    intro v hpv
    exact hS v ((mem_cubicAuxiliaryPrimeSet hp v).mpr hpv)
  have he := auxiliaryCubicSingularSeries_eq_modified_product (p : 𝓞 K) hp0 hν0 hgood σ
    (fun v => (hσ v).2) (fun v => (hσ v).1) hm
  have he' : auxiliaryCubicSingularSeries (p : 𝓞 K) hp0 ν =
      ((∏' v, if v ∈ S then cubicModifiedResidueFactor v ν else σ v : ℝ) : ℂ) := by
    simpa only [idealPrimeSupport_span_nat_eq_auxiliaryPrimeSet p hp, S] using he
  refine ⟨auxiliaryCubicCharacterContribution_norm_summable (p : 𝓞 K) hp0 ν hgood, ?_, ?_⟩
  · rw [he']; rfl
  · rw [he']; exact hlower

end WaringSiegel
#print axioms WaringSiegel.auxiliaryCubicSingularSeries_uniform_positive_173
