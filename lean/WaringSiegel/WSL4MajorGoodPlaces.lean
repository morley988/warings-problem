import WaringSiegel.WSL4ArchLocalGoodAll
import WaringSiegel.WSL3MomentLocalPowerProduct
import WaringSiegel.WSL4MajorTarget

/-! # Actual local solutions at every place not dividing the exponent -/
noncomputable section
set_option maxHeartbeats 900000
open IsLocalRing Filter
open scoped BigOperators NumberField Classical
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem completion_nat_isUnit_iff (k : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsUnit (k:v.adicCompletionIntegers K) ↔ (k:𝓞 K)∉v.asIdeal := by
  rw [← residue_ne_zero_iff_isUnit]
  simpa only [map_natCast] using not_congr (completion_residue_natCast_eq_zero_iff v k)

theorem exponent_dividing_places_finite (k : ℕ) (hk : 0<k) :
    Set.Finite {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | (k:𝓞 K)∈v.asIdeal} := by
  have h := Filter.mem_cofinite.mp (good_power_completion_primes_cofinite (K := K) k hk)
  simpa only [completion_nat_isUnit_iff,Set.compl_setOf,not_not] using h

theorem eligible_power_tuple_at_good_place (k s : ℕ) (hk : 0<k) (hs : k+1≤s)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : (k:𝓞 K)∉v.asIdeal)
    {ν : 𝓞 K} (hν : Eligible k ν) :
    ∃ x : Fin s → v.adicCompletionIntegers K,
      (∑ i,x i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧ ∃ i,IsUnit (x i) :=
  power_tuple_with_unit_mono k hk
    (power_tuple_in_completion_of_unit v k hk ((completion_nat_isUnit_iff k v).mpr hv) hν) hs

theorem localUnitSolvable_iff_at_exponent_divisors (k s : ℕ) (hk : 0<k) (hs : k+1≤s)
    {ν : 𝓞 K} (hν : Eligible k ν) :
    LocalUnitSolvable k s ν ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (k:𝓞 K)∈v.asIdeal →
        ∃ x : Fin s → v.adicCompletionIntegers K,
          (∑ i,x i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧ ∃ i,IsUnit (x i) := by
  constructor
  · intro h v _
    exact h v
  · intro h v
    by_cases hv : (k:𝓞 K)∈v.asIdeal
    · exact h v hv
    · exact eligible_power_tuple_at_good_place k s hk hs v hv hν

theorem optimized_bound_with_only_exponent_divisors
    (k s : ℕ) (hk : 3≤k) (hs : Thresholds.sufficientVariables k≤(s:ℤ)) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℝ, 0<N ∧ ∀ ν : 𝓞 K,
      TotallyPositive ν → Eligible k ν → N<absNorm ν →
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (k:𝓞 K)∈v.asIdeal →
        ∃ x : Fin s → v.adicCompletionIntegers K,
          (∑ i,x i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧ ∃ i,IsUnit (x i)) →
      RepresentableByAtMost k s C ν := by
  obtain ⟨_,hks⟩ := optimized_variables_arithmetic_range k s hk hs
  obtain ⟨C,hC,N,hN,hrep⟩ := optimized_localConditionalBound K k s hk hs
  refine ⟨C,hC,N,hN,?_⟩
  intro ν hpositive heligible hsize hbad
  exact hrep ν hpositive
    ((localUnitSolvable_iff_at_exponent_divisors k s (by omega) (by omega) heligible).mpr hbad) hsize

#print axioms exponent_dividing_places_finite
#print axioms eligible_power_tuple_at_good_place
#print axioms localUnitSolvable_iff_at_exponent_divisors
#print axioms optimized_bound_with_only_exponent_divisors
end WaringSiegel.WSL4
