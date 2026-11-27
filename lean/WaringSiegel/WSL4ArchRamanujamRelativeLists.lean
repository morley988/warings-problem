import WaringSiegel.WSL4WeilRelativePowers
import WaringSiegel.WSL4MajorRamanujamRelativeBound
import WaringSiegel.WSL4RamanujamPolynomialLists
import WaringSiegel.WSL4ArchRamanujamCoefficientDecomposition

/-! # Actual large-residue ideal terms as bounded lists of powers -/
noncomputable section
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
open WSL4Local
set_option maxHeartbeats 1500000
variable {B A : Type*} [CommRing B] [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]

theorem relative_maximal_power_term_list
    (f : B →+* A) (hsurj : Function.Surjective ((residue A).comp f))
    (hker : ∀b : B,residue A (f b)=0 ↔ (p:B)∣b)
    (n r k : ℕ) (hn : 0<n) (hnu : IsUnit (n:A)) (hkr : k≤r)
    (hspan : ∀a : ResidueField A,a∈AddSubgroup.closure (Set.range (fun x : ResidueField A => x^n)))
    (hcard : p^r<Nat.card (ResidueField A)) (w : A) (hw : w∈maximalIdeal A) :
    ∃l : List A,l.length≤4*(n*p^r)*(p^r+1) ∧
      localPowerListSum (n*p^r) l=(p:A)^(r-k)*w^(p^k) := by
  obtain ⟨c,z,hc,he⟩ := WSL4Weil.exists_relative_maximal_power_identity
    p r k (Fact.out : p.Prime) hkr n hnu f hsurj hker hcard w hw
  obtain ⟨l,hlen,hl⟩ := finite_sum_power_list Finset.univ (n*p^r)
    (fun j : Fin (p^r+1) => c j*(z j)^(n*p^r)) (fun _ => 4*(n*p^r)) (by
      intro j hj
      obtain ⟨l,hlen,hl⟩ := relativePrimeCoefficient_power_list p f hsurj hker n r hn hnu hspan (hc j)
      refine ⟨l.map (z j*·),by simpa only [List.length_map] using hlen,?_⟩
      rw [localPowerListSum_map_mul,hl,mul_comm])
  refine ⟨l,?_,hl.trans he⟩
  simpa [Nat.mul_comm] using hlen

theorem relative_ramanujamPowerTuple_list
    (f : B →+* A) (hsurj : Function.Surjective ((residue A).comp f))
    (hker : ∀b : B,residue A (f b)=0 ↔ (p:B)∣b)
    (n r : ℕ) (hn : 0<n) (hnu : IsUnit (n:A))
    (hspan : ∀a : ResidueField A,a∈AddSubgroup.closure (Set.range (fun x : ResidueField A => x^n)))
    (hcard : p^r<Nat.card (ResidueField A))
    (w : Fin (r+1) → A) (hw : ∀i,w i∈maximalIdeal A) :
    ∃l : List A,l.length≤4*(n*p^r)*(r+1)*(p^r+1) ∧
      localPowerListSum (n*p^r) l=ramanujamPowerTuple p r w := by
  obtain ⟨l,hlen,hl⟩ := finite_sum_power_list Finset.univ (n*p^r)
    (fun i : Fin (r+1) => (p:A)^i.val*w i^(p^(r-i.val)))
    (fun _ => 4*(n*p^r)*(p^r+1)) (by
      intro i hi
      have hir : i.val≤r := by omega
      simpa only [Nat.sub_sub_self hir] using
        relative_maximal_power_term_list p f hsurj hker n r (r-i.val) hn hnu
          (by omega) hspan hcard (w i) (hw i))
  refine ⟨l,?_,hl⟩
  simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hlen

#print axioms relative_maximal_power_term_list
#print axioms relative_ramanujamPowerTuple_list
end WaringSiegel.WSL4
