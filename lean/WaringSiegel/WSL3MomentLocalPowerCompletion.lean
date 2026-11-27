import WaringSiegel.WSL3MomentLocalPowerCount
import WaringSiegel.WSL3PowerFiniteDensity

/-!
# Actual completion counts and a finite-field-to-completion bridge for all k

At each finite place where k is a unit, a literal LocalUnitSolvable tuple
gives a target-independent positive lower bound for every normalized local
count. The explicit finite-field cutoff also produces actual unit solutions
in the completion, by the proved Hensel lift.
-/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing Filter Topology
open scoped NumberField BigOperators
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem completion_power_count_lower_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k s : ℕ) (hk : 0<k) (hku : IsUnit (k:v.adicCompletionIntegers K))
    {target : 𝓞 K} (hlocal : LocalUnitSolvable k (s+1) target) (n : ℕ) :
    Nat.card (ResidueField (v.adicCompletionIntegers K))^(s*n) ≤
      localPowerSolutionCount (v.adicCompletionIntegers K)
        (maximalIdeal (v.adicCompletionIntegers K)^(n+1)) k (s+1)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  obtain ⟨x,hx,hu⟩ := power_tuple_unit_first k (hlocal v)
  simpa only [hx] using local_power_count_lower_of_unit_tuple k hk hku x hu n

theorem completion_normalized_power_count_lower_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k s : ℕ) (hk : 0<k) (hku : IsUnit (k:v.adicCompletionIntegers K))
    {target : 𝓞 K} (hlocal : LocalUnitSolvable k (s+1) target) {e : ℕ} (he : 1≤e) :
    1/(Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ)^s ≤
      normalizedLocalPowerCount (v.adicCompletionIntegers K) k (s+1) e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le he
  obtain ⟨x,hx,hu⟩ := power_tuple_unit_first k (hlocal v)
  simpa only [hx,Nat.add_comm] using normalized_local_power_count_lower_of_unit_tuple k hk hku x hu n

theorem completion_power_density_limits_uniformly_positive
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k s : ℕ) (hk : 0<k) (hku : IsUnit (k:v.adicCompletionIntegers K)) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k (s+1) target → ∀ σ : ℝ,
      Tendsto (fun e => normalizedLocalPowerCount (v.adicCompletionIntegers K) k (s+1) e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)) atTop (𝓝 σ) → c≤σ := by
  letI := completionIntegers_residueFinite v
  have hq : 0<(Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) := by
    exact_mod_cast Nat.card_pos
  refine ⟨1/(Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ)^s,
    div_pos zero_lt_one (pow_pos hq _),?_⟩
  intro target hlocal σ hσ
  exact ge_of_tendsto hσ (eventually_atTop.mpr
    ⟨1,fun e he => completion_normalized_power_count_lower_bound v k s hk hku hlocal he⟩)

theorem completion_power_unit_solution_of_large_residue
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k s : ℕ) (hk : 0<k) (hs : 2≤s) (hku : IsUnit (k:v.adicCompletionIntegers K))
    (hq : 2*(k-1)^(2*s) ≤ Nat.card (ResidueField (v.adicCompletionIntegers K)))
    (target : 𝓞 K) :
    ∃ y : Fin (2*s) → v.adicCompletionIntegers K,
      (∑ i,y i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) target ∧
      ∃ i,IsUnit (y i) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers K))
  obtain ⟨x,hx,hu⟩ := finite_field_power_even_unit_solution k s hk hs
    (by simpa only [Nat.card_eq_fintype_card] using hq)
    (residue (v.adicCompletionIntegers K)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target))
  exact power_tuple_lift_of_nonzero_residue k hk hku x hx
    (by obtain ⟨i,hi⟩ := hu; exact ⟨i,hi.ne_zero⟩)

#print axioms completion_power_count_lower_bound
#print axioms completion_normalized_power_count_lower_bound
#print axioms completion_power_density_limits_uniformly_positive
#print axioms completion_power_unit_solution_of_large_residue
end WaringSiegel.WSL3
