import WaringSiegel.WSL3MomentLocalPowerRamifiedCount
import WaringSiegel.WSL3MomentLocalPowerCompletion

/-!
# Uniform positive all-degree local counts at every finite prime

For the literal LocalUnitSolvable hypothesis, the target-independent
precision is E=2v(k)+1, including every prime dividing k. Actual normalized
counts at precision e>=E are bounded below by q^(-(s-1)E).
No convergence assertion is assumed in the count bound. A convergent
density inherits its positive lower bound, with convergence stated openly.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing Filter Topology
open scoped NumberField BigOperators
namespace WaringSiegel.WSL3

theorem normalized_local_power_count_lower_of_count
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    {k s E n : ℕ} {a : R}
    (hc : Nat.card (ResidueField R)^(s*n) ≤
      localPowerSolutionCount R (maximalIdeal R^(n+E)) k (s+1) a) :
    1/(Nat.card (ResidueField R) : ℝ)^(s*E) ≤
      normalizedLocalPowerCount R k (s+1) (n+E) a := by
  have hq : 0<(Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hc' : (Nat.card (ResidueField R) : ℝ)^(s*n) ≤
      (localPowerSolutionCount R (maximalIdeal R^(n+E)) k (s+1) a : ℝ) := by exact_mod_cast hc
  unfold normalizedLocalPowerCount
  rw [Nat.add_sub_cancel]
  calc
    1/(Nat.card (ResidueField R) : ℝ)^(s*E)=
      (Nat.card (ResidueField R) : ℝ)^(s*n)/(Nat.card (ResidueField R) : ℝ)^(s*(n+E)) := by
        rw [Nat.mul_add,pow_add,← div_div,div_self (pow_ne_zero _ hq.ne')]
    _ ≤ _ := div_le_div_of_nonneg_right hc' (pow_pos hq _).le

variable {K : Type*} [Field K] [NumberField K]

theorem completion_power_count_lower_bound_all_primes
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k s : ℕ) (hk : 0<k)
    {target : 𝓞 K} (hlocal : LocalUnitSolvable k (s+1) target) (n : ℕ) :
    Nat.card (ResidueField (v.adicCompletionIntegers K))^(s*n) ≤
      localPowerSolutionCount (v.adicCompletionIntegers K)
        (maximalIdeal (v.adicCompletionIntegers K)^
          (n+powerLocalPrecision (v.adicCompletionIntegers K) k)) k (s+1)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  obtain ⟨x,hx,hu⟩ := power_tuple_unit_first k (hlocal v)
  have hE := power_stability_ideal_eq_power (v.adicCompletionIntegers K) k
    (by exact_mod_cast hk.ne')
  have h := local_power_count_lower_of_unit_tuple_ramified k hk x hu _ hE.le n
  simpa only [hx] using h

def completionPowerDensityLowerBound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k s : ℕ) : ℝ :=
  1/(Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ)^
    ((s-1)*powerLocalPrecision (v.adicCompletionIntegers K) k)

theorem completionPowerDensityLowerBound_pos
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k s : ℕ) :
    0<completionPowerDensityLowerBound v k s := by
  letI := completionIntegers_residueFinite v
  apply div_pos zero_lt_one
  apply pow_pos
  exact_mod_cast Nat.card_pos

theorem completion_normalized_power_count_lower_bound_all_primes
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k s : ℕ) (hk : 0<k)
    {target : 𝓞 K} (hlocal : LocalUnitSolvable k (s+1) target) {e : ℕ}
    (he : powerLocalPrecision (v.adicCompletionIntegers K) k≤e) :
    completionPowerDensityLowerBound v k (s+1) ≤
      normalizedLocalPowerCount (v.adicCompletionIntegers K) k (s+1) e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  letI := completionIntegers_residueFinite v
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le he
  have h := normalized_local_power_count_lower_of_count
    (completion_power_count_lower_bound_all_primes v k s hk hlocal n)
  simpa only [completionPowerDensityLowerBound,Nat.add_sub_cancel,Nat.add_comm] using h

theorem completion_power_density_limits_uniformly_positive_all_primes
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k s : ℕ) (hk : 0<k) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k (s+1) target → ∀ σ : ℝ,
      Tendsto (fun e => normalizedLocalPowerCount (v.adicCompletionIntegers K) k (s+1) e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)) atTop (𝓝 σ) → c≤σ := by
  refine ⟨completionPowerDensityLowerBound v k (s+1),
    completionPowerDensityLowerBound_pos v k (s+1),?_⟩
  intro target hlocal σ hσ
  exact ge_of_tendsto hσ (eventually_atTop.mpr
    ⟨powerLocalPrecision (v.adicCompletionIntegers K) k,
      fun e he => completion_normalized_power_count_lower_bound_all_primes v k s hk hlocal he⟩)

#print axioms completion_power_count_lower_bound_all_primes
#print axioms completion_normalized_power_count_lower_bound_all_primes
#print axioms completion_power_density_limits_uniformly_positive_all_primes
end WaringSiegel.WSL3
