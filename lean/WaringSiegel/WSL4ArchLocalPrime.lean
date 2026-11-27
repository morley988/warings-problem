import WaringSiegel.WSL4ArchLocalGood
import WaringSiegel.WSL4ArchLocalPrimeHelpers
import WaringSiegel.WSL4WeilJolyLocal

/-! # Unconditional Joly local unit solutions at every finite place

The two residue-characteristic branches are proved from finite-field
shortest representations and the integral Joly polynomial. The local
condition below is the original one, on actual completed integer rings.
-/
noncomputable section
open scoped BigOperators NumberField
open IsLocalRing
namespace WaringSiegel.WSL4
set_option maxHeartbeats 800000

theorem odd_prime_power_tuple_adic
    {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    (k : ℕ) (hkprime : Nat.Prime k) (hk : 3≤k) {a : A}
    (ha : a∈AddSubgroup.closure (Set.range (fun x : A => x^k))) :
    ∃x : Fin (2*k) → A,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  letI : Fact k.Prime := ⟨hkprime⟩
  by_cases hku : IsUnit (k:A)
  · letI : HenselianLocalRing A := henselianLocalRing_of_isAdicComplete
    exact odd_power_tuple_henselian_of_unit k (hkprime.odd_of_ne_two (by omega)) hku ha
  · letI : CharP (ResidueField A) k := residue_charP_of_prime_not_isUnit k hkprime hku
    have ha1 : a-1∈AddSubgroup.closure (Set.range (fun x : A => x^k)) :=
      (AddSubgroup.closure _).sub_mem ha (one_mem_power_closure k)
    obtain ⟨l,hlen,hl⟩ := WSL4Weil.eligible_odd_prime_power_list_bad_characteristic
      k (by omega) (a-1) ha1
    exact unit_power_tuple_of_short_list k (by omega) l (by omega) hl

theorem odd_prime_power_tuple_in_completion
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k : ℕ) (hkprime : Nat.Prime k) (hk : 3≤k) {ν : 𝓞 K} (hν : Eligible k ν) :
    ∃x : Fin (2*k) → v.adicCompletionIntegers K,
      (∑i,x i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧ ∃i,IsUnit (x i) := by
  letI := completionIntegers_isAdicComplete v
  letI := completionIntegers_residueFinite v
  exact odd_prime_power_tuple_adic k hkprime hk
    (map_mem_power_closure k (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) hν)

theorem eligible_odd_prime_localUnitSolvable
    {K : Type*} [Field K] [NumberField K]
    (k : ℕ) (hkprime : Nat.Prime k) (hk : 3≤k) {ν : 𝓞 K} (hν : Eligible k ν) :
    LocalUnitSolvable k (2*k) ν :=
  fun v => odd_prime_power_tuple_in_completion v k hkprime hk hν

theorem eligible_odd_prime_local_solvable
    {K : Type*} [Field K] [NumberField K]
    (k : ℕ) (hkprime : Nat.Prime k) (hk : 3≤k)
    {s : ℕ} (hs : 2*k≤s) {ν : 𝓞 K} (hν : Eligible k ν) :
    LocalUnitSolvable k s ν :=
  localUnitSolvable_mono k (by omega) (eligible_odd_prime_localUnitSolvable k hkprime hk hν) hs

#print axioms odd_prime_power_tuple_adic
#print axioms eligible_odd_prime_localUnitSolvable
#print axioms eligible_odd_prime_local_solvable
end WaringSiegel.WSL4
