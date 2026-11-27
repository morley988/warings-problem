import WaringSiegel.WSL3MomentLocalPowerProduct
import WaringSiegel.WSL3MomentLocalPowerVariableError

/-!
# Target-uniform local products for every variable count at least six

The finite-product assertion is unconditional under the literal local unit
solubility hypothesis. Statements about limits retain their convergence
hypotheses explicitly; no all-prime convergence result is claimed here.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem completion_power_count_all_finite_products_uniform_positive
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k p target →
      ∀ e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ,
        (∀ v,powerLocalPrecision (v.adicCompletionIntegers K) k≤e v) →
      ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        c≤∏ v∈S,normalizedLocalPowerCount (v.adicCompletionIntegers K) k p (e v)
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  obtain ⟨c,hc,hprod⟩ := uniform_positive_finite_products_of_lower_tails
    (powerEulerLowerError (K := K) k 3) (fun v => completionPowerDensityLowerBound v k p)
    (powerEulerLowerError_summable k 3) (fun _ => by unfold powerEulerLowerError; positivity)
    (fun v => IsUnit (k:v.adicCompletionIntegers K)) (good_power_completion_primes_cofinite k hk)
    (fun v => completionPowerDensityLowerBound_pos v k p)
  refine ⟨c,hc,?_⟩
  intro target hlocal e he S
  apply hprod _ ?_ ?_ S
  · intro v
    have hn : p-1+1=p := by omega
    have h := completion_normalized_power_count_lower_bound_all_primes v k (p-1) hk
      (by simpa only [hn] using hlocal) (he v)
    simpa only [hn] using h
  · intro v hv
    letI := completionIntegers_henselianLocalRing v
    letI := completionIntegers_residueFinite v
    have hvpos : 1≤e v := (powerLocalPrecision_pos (v.adicCompletionIntegers K) k).trans_le (he v)
    obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hvpos
    have h := normalized_local_power_all_variables_good_tail k p hk hp hv n
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)
    simpa only [powerEulerLowerError,show 2*3=6 from rfl,
      completion_residue_card_eq_absNorm,hn,Nat.add_comm] using h

theorem completion_power_density_finite_products_uniform_positive
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k p target →
      ∀ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v,Tendsto (fun e => normalizedLocalPowerCount (v.adicCompletionIntegers K) k p e
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)) atTop (𝓝 (σ v))) →
      ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),c≤∏ v∈S,σ v := by
  obtain ⟨c,hc,hfinite⟩ := completion_power_count_all_finite_products_uniform_positive (K := K) k p hk hp
  refine ⟨c,hc,?_⟩
  intro target hlocal σ hσ S
  have ht : Tendsto (fun n : ℕ => ∏ v∈S,
      normalizedLocalPowerCount (v.adicCompletionIntegers K) k p
        (n+powerLocalPrecision (v.adicCompletionIntegers K) k)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)) atTop (𝓝 (∏ v∈S,σ v)) := by
    apply tendsto_finset_prod
    intro v hv
    exact (hσ v).comp (tendsto_add_atTop_nat _)
  apply ge_of_tendsto ht
  exact Filter.Eventually.of_forall (fun n => hfinite target hlocal
    (fun v => n+powerLocalPrecision (v.adicCompletionIntegers K) k) (fun _ => by dsimp only; omega) S)

theorem completion_power_density_products_uniformly_positive_of_multipliable
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k p target →
      ∀ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v,Tendsto (fun e => normalizedLocalPowerCount (v.adicCompletionIntegers K) k p e
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)) atTop (𝓝 (σ v))) →
        Multipliable σ → c≤∏' v,σ v := by
  obtain ⟨c,hc,hfinite⟩ := completion_power_density_finite_products_uniform_positive (K := K) k p hk hp
  refine ⟨c,hc,?_⟩
  intro target hlocal σ hσ hprod
  exact ge_of_tendsto hprod.hasProd (Filter.Eventually.of_forall (hfinite target hlocal σ hσ))

#print axioms completion_power_count_all_finite_products_uniform_positive
#print axioms completion_power_density_finite_products_uniform_positive
#print axioms completion_power_density_products_uniformly_positive_of_multipliable
end WaringSiegel.WSL3
