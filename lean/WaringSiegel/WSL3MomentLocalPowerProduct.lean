import WaringSiegel.WSL3MomentLocalPowerTail
import WaringSiegel.WSL3MomentLocalPowerAllPrimes
import WaringSiegel.WSL2CubicEulerProduct

/-!
# Positive finite products from the actual all-degree local count bounds

No infinite-product convergence is postulated. A fixed positive comparison
product bounds every finite product of sufficiently precise local counts.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL3

theorem uniform_positive_finite_products_of_lower_tails {ι : Type*}
    (err lower : ι → ℝ) (herr : Summable err) (herr0 : ∀ i,0≤err i)
    (good : ι → Prop) (hgood : ∀ᶠ i in cofinite,good i) (hlower : ∀ i,0<lower i) :
    ∃ c : ℝ,0<c ∧ ∀ σ : ι → ℝ,(∀ i,lower i≤σ i) →
      (∀ i,good i → 1-err i≤σ i) → ∀ S : Finset ι,c≤∏ i∈S,σ i := by
  have hsmall : ∀ᶠ i in cofinite,err i<(1/2:ℝ) :=
    herr.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  have hboth := hgood.and hsmall
  let b : ι → ℝ := fun i => if good i ∧ err i<(1/2:ℝ) then 1-err i else min 1 (lower i)
  have hb (i : ι) : 0<b i := by
    dsimp [b]
    split_ifs with h
    · linarith [h.2]
    · exact lt_min zero_lt_one (hlower i)
  have hb1 (i : ι) : b i≤1 := by
    dsimp [b]
    split_ifs
    · linarith [herr0 i]
    · exact min_le_left _ _
  have hbsum : Summable (fun i => b i-1) := by
    apply herr.neg.congr_cofinite
    filter_upwards [hboth] with i hi
    dsimp [b]
    rw [if_pos hi]
    ring
  have hblog : Summable (fun i => Real.log (b i)) := by
    convert Real.summable_log_one_add_of_summable hbsum using 1
    funext i
    congr 1
    ring
  refine ⟨Real.exp (∑' i,Real.log (b i)),Real.exp_pos _,?_⟩
  intro σ hσlower hσtail S
  have hbσ (i : ι) : b i≤σ i := by
    dsimp [b]
    split_ifs with h
    · exact hσtail i h.1
    · exact (min_le_right _ _).trans (hσlower i)
  have hlog (i : ι) : Real.log (b i)≤0 := Real.log_nonpos (hb i).le (hb1 i)
  have htail : (∑' i : {i // i∉S},Real.log (b i))≤0 := tsum_nonpos (fun i => hlog i)
  have hsum : (∑' i,Real.log (b i))≤∑ i∈S,Real.log (b i) := by
    rw [← hblog.sum_add_tsum_subtype_compl S]
    linarith
  calc
    _ ≤ Real.exp (∑ i∈S,Real.log (b i)) := Real.exp_le_exp.mpr hsum
    _ = ∏ i∈S,b i := by rw [Real.exp_sum]; simp only [Real.exp_log (hb _)]
    _ ≤ _ := Finset.prod_le_prod (fun i _ => (hb i).le) (fun i _ => hbσ i)

variable {K : Type*} [Field K] [NumberField K]

theorem good_power_completion_primes_cofinite (k : ℕ) (hk : 0<k) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in cofinite,
      IsUnit (k:v.adicCompletionIntegers K) := by
  have hA : Ideal.span ({(k:𝓞 K)} : Set (𝓞 K))≠0 :=
    mt Ideal.span_singleton_eq_bot.mp (by exact_mod_cast hk.ne')
  have hfinite := (IdealDivisorBounds.idealDivisors_finite _ hA).preimage
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v _ w _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
  apply Filter.mem_cofinite.mpr
  apply hfinite.subset
  intro v hv
  have hu : ¬IsUnit (k:v.adicCompletionIntegers K) := by
    simpa only [Set.mem_compl_iff,Set.mem_setOf_eq] using hv
  have hr : (k:ResidueField (v.adicCompletionIntegers K))=0 := by
    by_contra hn
    apply hu
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using hn
  have hq : (k:𝓞 K ⧸ v.asIdeal)=0 := by
    apply (quotientCompletionResidueEquiv v).injective
    simpa only [map_natCast,map_zero] using hr
  change v.asIdeal ∣ Ideal.span ({(k:𝓞 K)} : Set (𝓞 K))
  rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_iff_mem]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_natCast] using hq)

def powerEulerLowerError (k s : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  (((k-1:ℕ):ℝ)^(2*s)+1)/(Ideal.absNorm v.asIdeal : ℝ)^2

theorem powerEulerLowerError_summable (k s : ℕ) :
    Summable (powerEulerLowerError (K := K) k s) := by
  have h := (primeIdeal_norm_rpow_summable (K := K) (by norm_num : (1:ℝ)<2)).mul_left
    (((k-1:ℕ):ℝ)^(2*s)+1)
  apply h.congr
  intro v
  simp only [powerEulerLowerError,Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_two,div_eq_mul_inv]

theorem completion_power_count_finite_products_uniform_positive
    (k s : ℕ) (hk : 0<k) (hs : 3≤s) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k (2*s) target →
      ∀ e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ,
        (∀ v,powerLocalPrecision (v.adicCompletionIntegers K) k≤e v) →
      ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        c≤∏ v∈S,normalizedLocalPowerCount (v.adicCompletionIntegers K) k (2*s) (e v)
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  obtain ⟨c,hc,hprod⟩ := uniform_positive_finite_products_of_lower_tails
    (powerEulerLowerError (K := K) k s) (fun v => completionPowerDensityLowerBound v k (2*s))
    (powerEulerLowerError_summable k s) (fun _ => by unfold powerEulerLowerError; positivity)
    (fun v => IsUnit (k:v.adicCompletionIntegers K)) (good_power_completion_primes_cofinite k hk)
    (fun v => completionPowerDensityLowerBound_pos v k (2*s))
  refine ⟨c,hc,?_⟩
  intro target hlocal e he S
  apply hprod _ ?_ ?_ S
  · intro v
    have hn : 2*s-1+1=2*s := by omega
    have h := completion_normalized_power_count_lower_bound_all_primes v k (2*s-1) hk
      (by simpa only [hn] using hlocal) (he v)
    simpa only [hn] using h
  · intro v hv
    letI := completionIntegers_henselianLocalRing v
    letI := completionIntegers_residueFinite v
    have hvpos : 1≤e v := (powerLocalPrecision_pos (v.adicCompletionIntegers K) k).trans_le (he v)
    obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hvpos
    have h := normalized_local_power_good_square_tail_lower k s hk hs hv n
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target)
    simpa only [powerEulerLowerError,completion_residue_card_eq_absNorm,hn,Nat.add_comm] using h

#print axioms good_power_completion_primes_cofinite
#print axioms completion_power_count_finite_products_uniform_positive
end WaringSiegel.WSL3
