import WaringSiegel.WSL4ArchLocalFiniteField
import WaringSiegel.WSL4ArchLocalTuples
import WaringSiegel.WSL3MomentLocalPowerLift
import WaringSiegel.CubicLocalTargets

/-! # Odd-power local solubility away from the exponent

The finite-field representation is an actual shortest-list theorem. Adding
the residue coordinate 1 makes the tuple nonsingular, and Hensel lifts it
in the actual completed integer ring.
-/
noncomputable section
open scoped BigOperators NumberField
open IsLocalRing
namespace WaringSiegel.WSL4
set_option maxHeartbeats 900000

theorem odd_power_tuple_henselian_of_unit
    {R : Type*} [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]
    (k : ℕ) (hk : Odd k) (hku : IsUnit (k:R)) {a : R}
    (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^k))) :
    ∃x : Fin (2*k) → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  have ha1 : a-1∈AddSubgroup.closure (Set.range (fun x : R => x^k)) :=
    (AddSubgroup.closure _).sub_mem ha (one_mem_power_closure k)
  have hres := map_mem_power_closure k (residue R) ha1
  obtain ⟨l,hlen,hl⟩ := finiteField_odd_power_list k hk (residue R (a-1)) hres
  let x : Fin (l.length+1) → ResidueField R := Fin.cons 1 l.get
  have hsum : (∑i,x i^k)=residue R a := by
    simp only [x,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_pow]
    rw [sum_power_get_eq_localPowerListSum,hl,map_sub,map_one]
    ring
  have hunit : ∃i,x i≠0 := ⟨0,by simp [x]⟩
  have hkpos : 0<k := hk.pos
  exact power_tuple_with_unit_mono k hk.pos
    (WSL3.power_tuple_lift_of_nonzero_residue k hk.pos hku x hsum hunit) (by omega)

theorem odd_power_tuple_in_completion_of_unit
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k : ℕ) (hk : Odd k) (hku : IsUnit (k:v.adicCompletionIntegers K))
    {ν : 𝓞 K} (hν : Eligible k ν) :
    ∃x : Fin (2*k) → v.adicCompletionIntegers K,
      (∑i,x i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧ ∃i,IsUnit (x i) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  exact odd_power_tuple_henselian_of_unit k hk hku
    (map_mem_power_closure k (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) hν)

#print axioms odd_power_tuple_henselian_of_unit
#print axioms odd_power_tuple_in_completion_of_unit
end WaringSiegel.WSL4
