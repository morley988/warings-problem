import WaringSiegel.WSL4RamanujamDeepPowers
import WaringSiegel.WSL4WeilGeometricDegreeBudget
import WaringSiegel.WSL4ArchRamanujamFinite
import Mathlib.Algebra.BigOperators.Intervals

/-! # One common summand budget for every deep truncated power expression -/
noncomputable section
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WSL4

def ramanujamDeepBudget (p n r : ℕ) : ℕ :=
  4*(n*p^r)*(p^r+1)*(p^r*(p^r+1)/2+1)

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]

theorem maximal_power_term_power_list_budget
    (p n r k : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R)) (hkr : k≤r)
    {pi : R} (hpi : Irreducible pi) (w : R)
    (hw : w∈(maximalIdeal R)^((n*p^r)*p^r+1)) :
    ∃l : List R,l.length≤ramanujamDeepBudget p n r*p^k ∧
      localPowerListSum (n*p^r) l=(p:R)^(r-k)*w^(p^k) := by
  obtain ⟨l,hlen,hl⟩ := maximal_power_term_power_list p n r k hn hnu hkr hpi w hw
  have hp : p.Prime := Fact.out
  have hd := WSL4Weil.geometric_degree_budget_sum_bound (p^r) (p^k)
    (Nat.one_le_pow _ _ hp.pos) (Nat.pow_le_pow_right hp.pos hkr)
  refine ⟨l,hlen.trans ?_,hl⟩
  rw [← Finset.mul_sum]
  calc
    _≤4*(n*p^r)*(p^k*(p^r+1)*(p^r*(p^r+1)/2+1)) := Nat.mul_le_mul_left _ hd
    _=ramanujamDeepBudget p n r*p^k := by unfold ramanujamDeepBudget; ring

theorem deep_ramanujamPowerTuple_power_list
    (p n r : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R))
    (w : Fin (r+1) → R) (hw : ∀i,w i∈(maximalIdeal R)^((n*p^r)*p^r+1)) :
    ∃l : List R,l.length≤ramanujamDeepBudget p n r*powerDigitBudget p (r+1) ∧
      localPowerListSum (n*p^r) l=ramanujamPowerTuple p r w := by
  obtain ⟨pi,hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨l,hlen,hl⟩ := finite_sum_power_list Finset.univ (n*p^r)
    (fun i : Fin (r+1) => (p:R)^i.val*w i^(p^(r-i.val)))
    (fun i => ramanujamDeepBudget p n r*p^(r-i.val)) (by
      intro i hi
      have hir : i.val≤r := by omega
      simpa only [Nat.sub_sub_self hir] using
        maximal_power_term_power_list_budget p n r (r-i.val) hn hnu (by omega) hpi (w i) (hw i))
  refine ⟨l,?_,hl⟩
  have hsum : (∑i : Fin (r+1),p^(r-i.val))=powerDigitBudget p (r+1) := by
    rw [powerDigitBudget_eq_sum,
      Fin.sum_univ_eq_sum_range (fun i => p^(r-i)) (r+1)]
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun i => p^i) (r+1)
  simpa only [← Finset.mul_sum,hsum] using hlen

#print axioms maximal_power_term_power_list_budget
#print axioms deep_ramanujamPowerTuple_power_list
end WaringSiegel.WSL4Local
