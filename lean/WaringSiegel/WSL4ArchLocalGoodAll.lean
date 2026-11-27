import WaringSiegel.WSL4ArchLocalFiniteAll
import WaringSiegel.WSL4ArchLocalGood

/-! # Every positive degree at places where the exponent is a unit -/
noncomputable section
open scoped BigOperators NumberField
open IsLocalRing
namespace WaringSiegel.WSL4
set_option maxHeartbeats 800000

theorem power_tuple_henselian_of_unit_of_finite_residue
    {R : Type*} [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:R)) {a : R}
    (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^k))) :
    ∃x : Fin (k+1) → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  have ha1 : a-1∈AddSubgroup.closure (Set.range (fun x : R => x^k)) :=
    (AddSubgroup.closure _).sub_mem ha (one_mem_power_closure k)
  have hres := map_mem_power_closure k (residue R) ha1
  obtain ⟨l,hlen,hl⟩ := finiteField_power_list k hk (residue R (a-1)) hres
  let x : Fin (l.length+1) → ResidueField R := Fin.cons 1 l.get
  have hsum : (∑i,x i^k)=residue R a := by
    simp only [x,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_pow]
    rw [sum_power_get_eq_localPowerListSum,hl,map_sub,map_one]
    ring
  have hunit : ∃i,x i≠0 := ⟨0,by simp [x]⟩
  exact power_tuple_with_unit_mono k hk
    (WSL3.power_tuple_lift_of_nonzero_residue k hk hku x hsum hunit) (by omega)

theorem power_tuple_in_completion_of_unit
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:v.adicCompletionIntegers K))
    {ν : 𝓞 K} (hν : Eligible k ν) :
    ∃x : Fin (k+1) → v.adicCompletionIntegers K,
      (∑i,x i^k)=algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧ ∃i,IsUnit (x i) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  exact power_tuple_henselian_of_unit_of_finite_residue k hk hku
    (map_mem_power_closure k (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) hν)

#print axioms power_tuple_henselian_of_unit_of_finite_residue
#print axioms power_tuple_in_completion_of_unit
end WaringSiegel.WSL4
