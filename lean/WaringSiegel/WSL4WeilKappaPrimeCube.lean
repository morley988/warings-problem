import WaringSiegel.WSL4WeilKappaLocalCube
import WaringSiegel.WSL2LocalAuxiliaryPrime

/-! # Uniform kappa comparison under a rational-prime cube multiplier -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped NumberField BigOperators Classical
open NumberField IsLocalRing WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem cubicKappa_bounded_good_cube_loss
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ) (hB : ∀v,0≤B v)
    (P I J : {I:Ideal (𝓞 K)//I≠0})
    (hP : ∀v∈idealPrimeSupport P.1 P.2,cubicKappaGood v=true ∧ (4:ℝ)≤Ideal.absNorm v.asIdeal)
    (hJI : ∀v,idealPrimeExponent J.1 v≤ idealPrimeExponent I.1 v)
    (hIJ : ∀v,idealPrimeExponent I.1 v≤ idealPrimeExponent J.1 v+3*idealPrimeExponent P.1 v) :
    cubicKappa B J≤(Ideal.absNorm P.1:ℝ)*cubicKappa B I := by
  let S := (idealPrimeSupport I.1 I.2∪idealPrimeSupport J.1 J.2)∪idealPrimeSupport P.1 P.2
  have hIS : idealPrimeSupport I.1 I.2⊆S := by intro v hv; exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hJS : idealPrimeSupport J.1 J.2⊆S := by intro v hv; exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hPS : idealPrimeSupport P.1 P.2⊆S := by intro v hv; exact Finset.mem_union_right _ hv
  have hprod : (∏v∈S,(Ideal.absNorm v.asIdeal:ℝ)^idealPrimeExponent P.1 v)=(Ideal.absNorm P.1:ℝ) := by
    rw [← Finset.prod_subset hPS (by
      intro v hv hvP
      rw [idealPrimeExponent_eq_zero_of_not_mem_support P.1 P.2 v hvP,pow_zero])]
    have h := congrArg (fun A : Ideal (𝓞 K)=>(Ideal.absNorm A:ℝ))
      (idealPrimeSupport_factorization P.1 P.2)
    simpa only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] using h
  rw [cubicKappa_eq_prod_superset B J S hJS,cubicKappa_eq_prod_superset B I S hIS,
    ← hprod,← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro v hv
    exact cubicKappaAt_nonneg _ _ _ _ (by positivity) (hB v)
  · intro v hv
    by_cases hvP : v∈idealPrimeSupport P.1 P.2
    · rw [(hP v hvP).1]
      exact cubicKappaAt_good_cube_loss _ _ (hP v hvP).2 _ _ _ (hIJ v)
    · have hzero := idealPrimeExponent_eq_zero_of_not_mem_support P.1 P.2 v hvP
      have he : idealPrimeExponent I.1 v=idealPrimeExponent J.1 v := by
        have h := hIJ v
        rw [hzero,mul_zero,add_zero] at h
        exact le_antisymm h (hJI v)
      simp only [hzero,pow_zero,one_mul,he,le_refl]

theorem idealPrimeExponent_cube (P : Ideal (𝓞 K)) (hP : P≠0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (P^3) v=3*idealPrimeExponent P v := by
  rw [pow_succ,pow_two,idealPrimeExponent_mul _ _ (mul_ne_zero hP hP) hP,
    idealPrimeExponent_mul P P hP hP]
  omega

/-- The comparison is uniform in the rational prime and permits ramification.
The large auxiliary primes used in the cubic argument satisfy 6<p. -/
theorem cubicKappa_prime_cube_mul_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ) (hB : ∀v,0≤B v)
    (p : ℕ) (hp : p.Prime) (hp6 : 6<p) (γ : K) :
    cubicKappa B ⟨traceConductor ((p:K)^3*γ),traceConductor_ne_zero ((p:K)^3*γ)⟩≤
      (p:ℝ)^Module.finrank ℚ K*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩ := by
  have hpO : (p:𝓞 K)≠0 := by exact_mod_cast hp.ne_zero
  let P : {I:Ideal (𝓞 K)//I≠0} :=
    ⟨Ideal.span ({(p:𝓞 K)} : Set (𝓞 K)),mt Ideal.span_singleton_eq_bot.mp hpO⟩
  have hgood : ∀v∈idealPrimeSupport P.1 P.2,cubicKappaGood v=true ∧ (4:ℝ)≤Ideal.absNorm v.asIdeal := by
    intro v hv
    have hd : v.asIdeal∣P.1 := (Ideal.finite_factors P.2).mem_toFinset.mp hv
    have hpv : (p:𝓞 K)∈v.asIdeal := (Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (by simp))
    have h6 := prime_above_large_rational_prime_avoids_six v hp hp6 hpv
    have h6' : (6:ResidueField (v.adicCompletionIntegers K))≠0 :=
      fun h=>h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
    refine ⟨by simp only [cubicKappaGood,decide_eq_true h6'],?_⟩
    exact_mod_cast (show 4≤Ideal.absNorm v.asIdeal from (by omega : 4≤p).trans (rational_prime_le_residue_norm v hp hpv))
  have hexp (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      idealPrimeExponent (Ideal.span ({(p:𝓞 K)^3} : Set (𝓞 K))) v=3*idealPrimeExponent P.1 v := by
    rw [← Ideal.span_singleton_pow]
    exact idealPrimeExponent_cube P.1 P.2 v
  have hb := cubicKappa_bounded_good_cube_loss B hB P
    ⟨traceConductor γ,traceConductor_ne_zero γ⟩
    ⟨traceConductor ((p:K)^3*γ),traceConductor_ne_zero ((p:K)^3*γ)⟩ hgood
    (fun v=>by
      simpa only [RingOfIntegers.coe_eq_algebraMap,map_pow,map_natCast] using
        (traceConductor_integral_mul_exponent_bounds ((p:𝓞 K)^3) (pow_ne_zero 3 hpO) γ v).1)
    (fun v=>by
      have h := (traceConductor_integral_mul_exponent_bounds ((p:𝓞 K)^3) (pow_ne_zero 3 hpO) γ v).2
      rw [hexp] at h
      simpa only [RingOfIntegers.coe_eq_algebraMap,map_pow,map_natCast] using h)
  simpa only [P,ideal_absNorm_span_nat,Nat.cast_pow] using hb
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.cubicKappa_prime_cube_mul_bound
