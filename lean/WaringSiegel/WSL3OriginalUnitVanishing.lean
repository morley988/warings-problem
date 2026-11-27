import WaringSiegel.WSL3LocalUnitVanishing

/-! # WSL3: the exact prime-power conductor cutoff for original unit cubic sums -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem finiteRingUnitPowerSum_congr
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (e : R ≃+* S) (ψ : AddChar R ℂ) (k : ℕ) :
    finiteRingUnitPowerSum (ψ.compAddMonoidHom e.symm.toAddMonoidHom) k =
      finiteRingUnitPowerSum ψ k := by
  have he := (Units.mapEquiv e.symm.toMulEquiv).bijective.sum_comp
    (fun x : Rˣ => ψ ((x : R)^k))
  simp only [Units.coe_mapEquiv] at he
  change (∑ x : Sˣ, ψ (e.symm ((x : S)^k))) = ∑ x : Rˣ, ψ ((x : R)^k)
  simpa only [map_pow] using he


variable {K : Type*} [Field K] [NumberField K]

/-- A primitive character of conductor v^(n+1), n>=1, gives zero pure
unit cubic sum in the original quotient, at every prime away from 6. -/
theorem original_primitive_unit_cubic_sum_vanishes
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (𝓞 K ⧸ v.asIdeal^(n+1))]
    (ψ : AddChar (𝓞 K ⧸ v.asIdeal^(n+1)) ℂ)
    (hψ : quotientCharacterConductor (v.asIdeal^(n+1)) ψ = v.asIdeal^(n+1)) :
    finiteRingUnitPowerSum ψ 3 = 0 := by
  let R := v.adicCompletionIntegers K
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := dvr_power_quotient_finite (R := R) (n+1)
  letI := Fintype.ofFinite (R ⧸ maximalIdeal R^(n+1))
  let e := primePowerCompletionEquiv v (n+1)
  let φ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hC : ¬v.asIdeal ≤ quotientCharacterConductor (v.asIdeal^(n+1)) ψ := by
    rw [hψ]
    intro h
    have hd : v.asIdeal^(n+1) ∣ v.asIdeal^1 := Ideal.dvd_iff_le.mpr (by simpa using h)
    have hh := (pow_dvd_pow_iff v.prime.ne_zero v.prime.not_unit).mp hd
    omega
  have hw : ∃ a : 𝓞 K, a ∈ v.asIdeal ∧
      ∃ x : 𝓞 K, ψ (Ideal.Quotient.mk (v.asIdeal^(n+1)) (a*x)) ≠ 1 := by
    by_contra h
    push_neg at h
    apply hC
    intro a ha x
    exact h a ha x
  obtain ⟨a,ha,x,hax⟩ := hw
  have ha' : algebraMap (𝓞 K) R a ∈ maximalIdeal R := by
    simpa only [pow_one] using (completion_mem_maximalIdeal_pow_iff v a 1).mpr
      (by simpa only [pow_one] using ha)
  have hφ : ¬maximalIdeal R ≤ quotientCharacterConductor (maximalIdeal R^(n+1)) φ := by
    intro h
    have hh := h ha' (algebraMap (𝓞 K) R x)
    apply hax
    change φ (Ideal.Quotient.mk (maximalIdeal R^(n+1))
      (algebraMap (𝓞 K) R a * algebraMap (𝓞 K) R x)) = 1 at hh
    rw [← map_mul] at hh
    change ψ (e.symm (e (Ideal.Quotient.mk (v.asIdeal^(n+1)) (a*x)))) = 1 at hh
    simpa only [e.symm_apply_apply] using hh
  have h6' : (6 : ResidueField R) ≠ 0 := by
    intro h
    exact h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hz := local_unit_cubic_sum_vanishes (three_isUnit_of_six_residue_ne_zero h6') n φ hφ
  rw [finiteRingUnitPowerSum_congr e ψ 3] at hz
  exact hz

theorem original_primitive_restricted_cubic_term_vanishes
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (𝓞 K ⧸ v.asIdeal^(n+1))]
    (ψ : AddChar (𝓞 K ⧸ v.asIdeal^(n+1)) ℂ)
    (hψ : quotientCharacterConductor (v.asIdeal^(n+1)) ψ = v.asIdeal^(n+1))
    (p ν : 𝓞 K) :
    finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.mk (v.asIdeal^(n+1)) p)
      (Ideal.Quotient.mk (v.asIdeal^(n+1)) ν) ψ = 0 := by
  unfold finiteRingRestrictedCubicCharacterTerm
  rw [original_primitive_unit_cubic_sum_vanishes v h6 n hn ψ hψ,
    zero_div, zero_pow (by decide), zero_mul, zero_mul]

end WaringSiegel
#print axioms WaringSiegel.original_primitive_unit_cubic_sum_vanishes
#print axioms WaringSiegel.original_primitive_restricted_cubic_term_vanishes
