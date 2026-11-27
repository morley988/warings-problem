import WaringSiegel.WSL3CubicKappaIdeal

/-! # Conductor control under a fixed integral multiplier -/
noncomputable section
open IsLocalRing NumberField
open scoped NumberField BigOperators Classical nonZeroDivisors
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem traceConductor_le_integral_mul (c : 𝓞 K) (γ : K) :
    traceConductor γ≤traceConductor ((c:K)*γ) := by
  intro a ha
  have h := (traceConductor γ).mul_mem_left c ha
  change ((a:K)*((c:K)*γ))∈inverseDifferent K
  change (((c*a:𝓞 K):K)*γ)∈inverseDifferent K at h
  simpa only [RingOfIntegers.coe_eq_algebraMap,map_mul,mul_assoc,mul_left_comm] using h

theorem span_mul_traceConductor_le (c : 𝓞 K) (γ : K) :
    Ideal.span ({c}:Set (𝓞 K))*traceConductor ((c:K)*γ)≤traceConductor γ := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro a ha
  change (((c*a:𝓞 K):K)*γ)∈inverseDifferent K
  change ((a:K)*((c:K)*γ))∈inverseDifferent K at ha
  simpa only [RingOfIntegers.coe_eq_algebraMap,map_mul,mul_assoc,mul_left_comm] using ha

theorem traceConductor_integral_mul_norm_le (c : 𝓞 K) (γ : K) :
    (traceConductor ((c:K)*γ)).absNorm≤(traceConductor γ).absNorm :=
  Nat.le_of_dvd (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ)
    (Ideal.absNorm_dvd_absNorm_of_le (traceConductor_le_integral_mul c γ))

theorem idealPrimeExponent_mono {I J : Ideal (𝓞 K)} (hJ : J≠0) (hIJ : I∣J)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent I v ≤ idealPrimeExponent J v :=
  Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hJ)
    (Associates.irreducible_mk.mpr v.irreducible) (Associates.mk_le_mk_of_dvd hIJ)

theorem idealPrimeExponent_mul (I J : Ideal (𝓞 K)) (hI : I≠0) (hJ : J≠0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (I*J) v=idealPrimeExponent I v+idealPrimeExponent J v := by
  unfold idealPrimeExponent
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    (Associates.irreducible_mk.mpr v.irreducible)

theorem traceConductor_integral_mul_exponent_bounds (c : 𝓞 K) (hc : c≠0) (γ : K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (traceConductor ((c:K)*γ)) v ≤ idealPrimeExponent (traceConductor γ) v ∧
      idealPrimeExponent (traceConductor γ) v≤
        idealPrimeExponent (traceConductor ((c:K)*γ)) v+
          idealPrimeExponent (Ideal.span ({c}:Set (𝓞 K))) v := by
  have hA : Ideal.span ({c}:Set (𝓞 K))≠0 := mt Ideal.span_singleton_eq_bot.mp hc
  constructor
  · exact idealPrimeExponent_mono (traceConductor_ne_zero γ)
      (Ideal.dvd_iff_le.mpr (traceConductor_le_integral_mul c γ)) v
  · have h := idealPrimeExponent_mono
      (mul_ne_zero hA (traceConductor_ne_zero ((c:K)*γ)))
      (Ideal.dvd_iff_le.mpr (span_mul_traceConductor_le c γ)) v
    rw [idealPrimeExponent_mul _ _ hA (traceConductor_ne_zero ((c:K)*γ))] at h
    simpa only [Nat.add_comm] using h

theorem idealPrimeExponent_eq_zero_of_not_mem_support
    (I : Ideal (𝓞 K)) (hI : I≠0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : v∉idealPrimeSupport I hI) :
    idealPrimeExponent I v=0 := by
  apply not_ne_iff.mp
  intro hn
  apply hv
  exact (Ideal.finite_factors hI).mem_toFinset.mpr
    ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hn)

theorem cubicKappaGood_eq_false_of_four_support
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v∈idealPrimeSupport (Ideal.span ({(4:𝓞 K)}:Set (𝓞 K)))
      (mt Ideal.span_singleton_eq_bot.mp (by norm_num))) :
    cubicKappaGood v=false := by
  have hd : v.asIdeal∣Ideal.span ({(4:𝓞 K)}:Set (𝓞 K)) :=
    (Ideal.finite_factors (mt Ideal.span_singleton_eq_bot.mp (by norm_num : (4:𝓞 K)≠0))).mem_toFinset.mp hv
  have h4 : (4:𝓞 K)∈v.asIdeal := (Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (by simp))
  have h4' : (4:ResidueField (v.adicCompletionIntegers K))=0 :=
    (completion_residue_natCast_eq_zero_iff v 4).mpr h4
  have h2 : (2:ResidueField (v.adicCompletionIntegers K))=0 := by
    have hh : (2:ResidueField (v.adicCompletionIntegers K))^2=0 := by norm_num at h4' ⊢; exact h4'
    exact pow_eq_zero hh
  have h6 : (6:ResidueField (v.adicCompletionIntegers K))=0 := by
    calc
      _=(2:ResidueField (v.adicCompletionIntegers K))*3 := by norm_num
      _=0 := by rw [h2,zero_mul]
  simp only [cubicKappaGood,h6,ne_eq,not_true_eq_false,decide_false]

#print axioms traceConductor_integral_mul_norm_le
#print axioms traceConductor_integral_mul_exponent_bounds
#print axioms cubicKappaGood_eq_false_of_four_support
end WaringSiegel.WSL4Local
