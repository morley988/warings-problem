import WaringSiegel.WSL4RamanujamPolynomialLists
import WaringSiegel.WSL4WeilGeometricPowers

/-! # Deep local-ideal terms represented by bounded lists of actual powers -/
noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WSL4
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]

theorem maximal_power_term_power_list
    (p n r k : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R)) (hkr : k≤r)
    {pi : R} (hpi : Irreducible pi) (w : R)
    (hw : w∈(maximalIdeal R)^((n*p^r)*p^r+1)) :
    ∃l : List R,
      l.length≤∑j : Fin (p^r+1),4*(n*p^r)*
        ((p^k+1)*(p^r-p^k)+(p^k-1)*(p^r*(p^r+1)/2)+j.val*(p^r-j.val)+1) ∧
      localPowerListSum (n*p^r) l=(p:R)^(r-k)*w^(p^k) := by
  obtain ⟨Q,z,hdegree,hcoeff,heq⟩ := WSL4Weil.exists_maximal_power_coefficient_identity
    p r k Fact.out hkr n hn hnu hpi w hw
  obtain ⟨l,hlen,hl⟩ := finite_sum_power_list Finset.univ (n*p^r)
    (fun j : Fin (p^r+1) => (Q j).eval (pi^(n*p^r))*(z j)^(n*p^r))
    (fun j => 4*(n*p^r)*
      ((p^k+1)*(p^r-p^k)+(p^k-1)*(p^r*(p^r+1)/2)+j.val*(p^r-j.val)+1)) (by
      intro j hj
      obtain ⟨l,hlen,hl⟩ := polynomial_eval_power_list (Q j) (n*p^r) (4*(n*p^r)) _ pi
        (hdegree j) (fun i hi => rationalPrimeCoefficient_power_list_sharp p n r hn hnu (hcoeff j i))
      refine ⟨l.map (z j*·),by simpa using hlen,?_⟩
      rw [localPowerListSum_map_mul,hl,mul_comm])
  exact ⟨l,hlen,hl.trans heq⟩

#print axioms maximal_power_term_power_list
end WaringSiegel.WSL4Local
