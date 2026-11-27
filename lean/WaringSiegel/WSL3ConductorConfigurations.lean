import WaringSiegel.WSL3ConductorFactorization

/-! # WSL3: finite prime-support coordinates for the ideal singular series -/
noncomputable section
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def ConductorConfiguration (K : Type*) [Field K] [NumberField K] :=
  Σ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)), S → ℕ

def configurationExponent (c : ConductorConfiguration K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  if h : v ∈ c.1 then c.2 ⟨v,h⟩ + 1 else 0

def configurationIdeal (c : ConductorConfiguration K) : {I : Ideal (𝓞 K) // I ≠ 0} :=
  ⟨∏ v ∈ c.1, v.asIdeal^configurationExponent c v,
    prime_power_product_ne_zero c.1 (configurationExponent c)⟩

theorem configurationIdeal_support (c : ConductorConfiguration K) :
    idealPrimeSupport (configurationIdeal c).1 (configurationIdeal c).2 = c.1 := by
  apply idealPrimeSupport_finset_prod
  intro v hv
  simp only [configurationExponent, dif_pos hv]
  omega

theorem configurationIdeal_exponent (c : ConductorConfiguration K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (configurationIdeal c).1 v = configurationExponent c v := by
  change idealPrimeExponent (∏ w ∈ c.1, w.asIdeal^configurationExponent c w) v = _
  rw [idealPrimeExponent_finset_prod]
  by_cases hv : v ∈ c.1
  · rw [if_pos hv]
  · simp [configurationExponent, hv]

theorem configurationIdeal_injective :
    Function.Injective (configurationIdeal (K := K)) := by
  rintro ⟨S,n⟩ ⟨T,m⟩ h
  have hST : S = T := by
    simpa only [configurationIdeal_support] using congrArg
      (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => idealPrimeSupport I.1 I.2) h
  subst T
  congr 1
  funext v
  have he := congrArg (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
    idealPrimeExponent I.1 v.1) h
  simp only [configurationIdeal_exponent, configurationExponent, dif_pos v.2] at he
  exact Nat.add_right_cancel he

theorem configurationIdeal_surjective :
    Function.Surjective (configurationIdeal (K := K)) := by
  intro I
  let c : ConductorConfiguration K :=
    ⟨idealPrimeSupport I.1 I.2, fun v => idealPrimeExponent I.1 v.1 - 1⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change (∏ v ∈ idealPrimeSupport I.1 I.2, v.asIdeal^configurationExponent c v) = I.1
  calc
    _ = ∏ v ∈ idealPrimeSupport I.1 I.2, v.asIdeal^idealPrimeExponent I.1 v := by
      apply Finset.prod_congr rfl
      intro v hv
      simp only [configurationExponent, c, dif_pos hv]
      rw [Nat.sub_add_cancel (idealPrimeExponent_pos_of_mem I.1 I.2 v hv)]
    _ = I.1 := idealPrimeSupport_factorization I.1 I.2

def conductorConfigurationEquiv :
    ConductorConfiguration K ≃ {I : Ideal (𝓞 K) // I ≠ 0} :=
  Equiv.ofBijective configurationIdeal
    ⟨configurationIdeal_injective, configurationIdeal_surjective⟩

theorem idealPrimitiveCubicCoefficient_configuration
    (c : ConductorConfiguration K) (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient (configurationIdeal c).1 (configurationIdeal c).2 ν =
      ∏ v : c.1, primePowerPrimitiveCubicCoefficient v.1 (c.2 v+1) ν := by
  rw [configurationIdeal, idealPrimitiveCubicCoefficient_finset_prod]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro v _
  simp only [configurationExponent, dif_pos v.2]

end WaringSiegel
