import WaringSiegel.WSL3AuxiliaryIdealSplit
import WaringSiegel.WSL3AuxiliaryBadProduct

/-! # Uniform finite auxiliary complete-sum mass on an actual common modulus

Every ambient modulus M is split into its genuine prime factors over the
mask P=(p) and the relatively prime remaining factor. The bad factors cost
at most Norm(P)^2, including arbitrary ramification exponents.
-/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem idealMaskedConductorMass_global_bound
    (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0) (hMP : M ≤ P)
    (p ν : 𝓞 K) (hPspan : P = Ideal.span ({p}:Set (𝓞 K)))
    (h6 : ∀ v ∈ idealPrimeSupport P hP, (6:𝓞 K) ∉ v.asIdeal)
    (hq : ∀ v ∈ idealPrimeSupport P hP, 173 ≤ Ideal.absNorm v.asIdeal) :
    idealMaskedConductorMass M hM P hMP p ν (5/4:ℝ) ≤
      cubicSharpUniformSingularSeriesConstant K*(Ideal.absNorm P:ℝ)^2 := by
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
  have hb := idealMaskedConductorMass_good_bad_product_le J hJ S r e he her h6 hq hcop p ν hpJ hpv
  have heM : J*(∏ v ∈ S, v.asIdeal^r v)=M := auxiliaryGoodIdeal_mul_bad M P hM hP hMP
  have heP : (∏ v ∈ S, v.asIdeal^e v)=P := idealPrimeSupport_factorization P hP
  have hb' : idealMaskedConductorMass M hM P hMP p ν (5/4:ℝ) ≤
      cubicSharpUniformSingularSeriesConstant K*∏ v ∈ S, (Ideal.absNorm v.asIdeal:ℝ)^2 := by
    simpa only [heM,heP] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_left (idealPrimeSupport_norm_square_le P hP)
    cubicSharpUniformSingularSeriesConstant_pos.le)

/-- The same actual finite mass in the precise interface needed for the
finite-to-infinite exact-conductor summability theorem. -/
theorem finiteMaskedConductorMass_global_bound
    (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0) (hMP : M ≤ P)
    (p ν : 𝓞 K) (hPspan : P = Ideal.span ({p}:Set (𝓞 K)))
    (h6 : ∀ v ∈ idealPrimeSupport P hP, (6:𝓞 K) ∉ v.asIdeal)
    (hq : ∀ v ∈ idealPrimeSupport P hP, 173 ≤ Ideal.absNorm v.asIdeal) :
    letI := idealResidueFintype M hM
    finiteMaskedConductorMass M P hMP p ν (5/4:ℝ) ≤
      cubicSharpUniformSingularSeriesConstant K*(Ideal.absNorm P:ℝ)^2 := by
  exact idealMaskedConductorMass_global_bound M P hM hP hMP p ν hPspan h6 hq

end WaringSiegel
#print axioms WaringSiegel.idealMaskedConductorMass_global_bound
#print axioms WaringSiegel.finiteMaskedConductorMass_global_bound
