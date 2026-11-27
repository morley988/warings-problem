import WaringSiegel.WSL4RamanujamWildBudget
import WaringSiegel.WSL4ArchRamanujamDVRDecomposition

/-! # The strict local polynomial bound at bounded residue degree

The residue-field cardinality may be arbitrarily large. Only its degree
f over F_p is assumed smaller than the exponent. All ramification indices
are allowed. The final list consists of actual roots in the completed ring.
-/
noncomputable section
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WSL4
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]

theorem small_residue_degree_power_list
    (p n r f : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R)) (hr : 1≤r)
    (hm : 4≤n*p^r) (hf : f<n*p^r) (hres : Nat.card (ResidueField R)=p^f)
    (a : R) (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^(n*p^r)))) :
    ∃l : List R,l.length<8*(n*p^r)^5 ∧ localPowerListSum (n*p^r) l=a := by
  have hp : p.Prime := Fact.out
  let t := ramanujamLiftPrecision p r
  let Y := (n*p^r)*p^r+1
  have hrt : r+1≤t := by
    have h := ramanujamLiftOffset_pos p
    dsimp [t,ramanujamLiftPrecision]
    omega
  have has : a-1∈AddSubgroup.closure (Set.range (fun x : R => x^(n*p^r))) :=
    (AddSubgroup.closure _).sub_mem ha (one_mem_power_closure (n*p^r))
  obtain ⟨l,w,z,hlen,hw,he⟩ := dvr_eligible_power_list_deep_remainder
    n r t Y f hrt hres (a-1) has
  obtain ⟨q,hqlen,hq⟩ := deep_ramanujamPowerTuple_power_list p n r hn hnu w hw
  let L := l++q
  have hL : localPowerListSum (n*p^r) L=
      localPowerListSum (n*p^r) l+ramanujamPowerTuple p r w := by
    change localPowerListSum (n*p^r) (l++q)=_
    rw [localPowerListSum_append,hq]
  have hdvd : (p:R)^t∣(a-localPowerListSum (n*p^r) L)-(1:R)^(n*p^r) := by
    refine ⟨z,?_⟩
    rw [one_pow,hL]
    linear_combination he
  obtain ⟨y,hy,_,_⟩ := power_root_of_dvd_sharp p n r hp hnu 1
    (a-localPowerListSum (n*p^r) L) isUnit_one hdvd
  refine ⟨y::L,?_,?_⟩
  · have hbudget := full_wild_natural_budget_lt p n r f hp.two_le hn hr hm hf
    have hlen' : (y::L).length≤ramanujamDeepBudget p n r*powerDigitBudget p (r+1)+
        Y*f*(p^t-1)+1 := by
      simp only [List.length_cons,L,List.length_append]
      omega
    exact hlen'.trans_lt (by
      simpa only [Y,t,ramanujamLiftPrecision,ramanujamLiftOffset] using hbudget)
  · rw [localPowerListSum_cons,hy]
    ring

#print axioms small_residue_degree_power_list
end WaringSiegel.WSL4Local
