import WaringSiegel.WSL3AuxiliaryEulerFinite

/-! # Exact finite replacement identity for the literal auxiliary series -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem idealMaskedCubicSum_good_bad_product
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (he : ∀ v ∈ S, 1 ≤ e v) (her : ∀ v ∈ S, e v ≤ r v)
    (h6 : ∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal)
    (hcop : IsCoprime J (∏ v ∈ S, v.asIdeal^r v)) (p ν : 𝓞 K)
    (hpJ : IsUnit (Ideal.Quotient.mk J p)) (hpv : ∀ v ∈ S, p ∈ v.asIdeal) :
    idealMaskedCubicSum (J*(∏ v ∈ S, v.asIdeal^r v))
      (mul_ne_zero hJ (prime_power_product_ne_zero S r))
      (∏ v ∈ S, v.asIdeal^e v)
      (Ideal.mul_le_left.trans (prime_power_product_le S r e her)) p ν =
      idealOrdinaryCubicSum J hJ ν * ∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ) := by
  have hh := idealMaskedCubicSum_mul J (∏ v ∈ S, v.asIdeal^r v)
    ⊤ (∏ v ∈ S, v.asIdeal^e v) hJ (prime_power_product_ne_zero S r)
    hcop le_top (prime_power_product_le S r e her) p ν
  simpa only [Ideal.top_mul, idealMaskedCubicSum_unrestricted J hJ p ν hpJ,
    idealMaskedCubicSum_bad_product S r e he her h6 p ν hpv] using hh

/-- No limiting argument is used here. Both sides contain the literal full
character sums on the ambient quotient, with the actual finite local counts. -/
theorem idealMaskedCubicSum_finite_replacement
    (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0) (hMP : M ≤ P)
    (p ν : 𝓞 K) (hPspan : P = Ideal.span ({p}:Set (𝓞 K)))
    (h6 : ∀ v ∈ idealPrimeSupport P hP, (6:𝓞 K) ∉ v.asIdeal) :
    idealMaskedCubicSum M hM P hMP p ν *
        (∏ v ∈ idealPrimeSupport P hP,
          (normalizedPrimePowerCubicCount v 8 (idealPrimeExponent M v) ν : ℂ)) =
      idealOrdinaryCubicSum M hM ν *
        (∏ v ∈ idealPrimeSupport P hP, (cubicModifiedResidueFactor v ν : ℂ)) := by
  let S := idealPrimeSupport P hP
  let r := idealPrimeExponent M
  let e := idealPrimeExponent P
  let J := auxiliaryGoodIdeal M hM P hP
  have hJ : J ≠ 0 := auxiliaryGoodIdeal_ne_zero M hM P hP
  have he : ∀ v ∈ S, 1 ≤ e v := fun v hv => idealPrimeExponent_pos_of_mem P hP v hv
  have her : ∀ v ∈ S, e v ≤ r v := fun v _ => idealPrimeExponent_mono_of_le M P hM hP hMP v
  have hcop : IsCoprime J (∏ v ∈ S, v.asIdeal^r v) := auxiliaryGoodIdeal_coprime_bad M hM P hP
  have hcopP : IsCoprime J P := auxiliaryGoodIdeal_coprime_mask M hM P hP
  have hpJ : IsUnit (Ideal.Quotient.mk J p) :=
    isUnit_quotient_mk_of_coprime_span J p (by simpa only [hPspan] using hcopP)
  have hpP : p ∈ P := by rw [hPspan]; exact Ideal.subset_span (Set.mem_singleton p)
  have hpv : ∀ v ∈ S, p ∈ v.asIdeal := by
    intro v hv
    exact (Ideal.dvd_iff_le.mp ((mem_idealPrimeSupport_iff_dvd P hP v).mp hv)) hpP
  have hb := idealMaskedCubicSum_good_bad_product J hJ S r e he her h6 hcop p ν hpJ hpv
  have heM : J*(∏ v ∈ S, v.asIdeal^r v)=M := auxiliaryGoodIdeal_mul_bad M P hM hP hMP
  have heP : (∏ v ∈ S, v.asIdeal^e v)=P := idealPrimeSupport_factorization P hP
  have hb' : idealMaskedCubicSum M hM P hMP p ν =
      idealOrdinaryCubicSum J hJ ν * ∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ) := by
    simpa only [heM,heP] using hb
  have ho := idealOrdinaryCubicSum_mul J (∏ v ∈ S, v.asIdeal^r v)
    hJ (prime_power_product_ne_zero S r) hcop ν
  rw [idealOrdinaryCubicSum_finset_prod] at ho
  have ho' : idealOrdinaryCubicSum M hM ν =
      idealOrdinaryCubicSum J hJ ν *
        ∏ v ∈ S, (normalizedPrimePowerCubicCount v 8 (r v) ν : ℂ) := by
    simpa only [heM] using ho
  change idealMaskedCubicSum M hM P hMP p ν *
      (∏ v ∈ S, (normalizedPrimePowerCubicCount v 8 (r v) ν : ℂ)) =
    idealOrdinaryCubicSum M hM ν * ∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ)
  rw [hb',ho']
  ring

end WaringSiegel
#print axioms WaringSiegel.idealMaskedCubicSum_finite_replacement
