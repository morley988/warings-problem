import WaringSiegel.WSL4ArchRamanujamRelativeLists
import WaringSiegel.WSL4ArchRamanujamLargeBudget

/-! # The strict polynomial local bound at large residue degree

The coefficient algebra, all coefficient power lists, interpolation nodes,
and ideal-term lists are constructed. No unramified embedding is assumed.
-/
noncomputable section
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1800000
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]

theorem large_residue_degree_power_list
    (p n r f : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R))
    (hm : 2≤n*p^r) (hf : n*p^r≤f) (hres : Nat.card (ResidueField R)=p^f)
    (a : R) (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^(n*p^r)))) :
    ∃l : List R,l.length<8*(n*p^r)^5 ∧ localPowerListSum (n*p^r) l=a := by
  have hp : p.Prime := Fact.out
  letI : Algebra (ZMod p) (ResidueField R) := ZMod.algebra _ _
  have hnf : n≤f := large_residue_degree_tame_le p n r f hp hf
  have hspan : ∀b : ResidueField R,
      b∈AddSubgroup.closure (Set.range (fun x : ResidueField R => x^n)) :=
    finiteField_power_closure_of_residue_degree p f n hp hn hres hnf
  have hcard : p^r<Nat.card (ResidueField R) :=
    large_residue_degree_node_card p n r f hp hn hres hf
  obtain ⟨F,hmon,hdeg,g,hs,hk,hcoeff⟩ :=
    exists_monogenic_coefficient_power_bound (A:=R) p n r hn hnu hspan
  obtain ⟨b,w,hw,he⟩ := eligible_coefficient_ghost_decomposition (p:=p) n r
    (maximalIdeal R) g hs a ha
  obtain ⟨l,hlen,hl⟩ := hcoeff (g b) (mem_relativePrimeCoefficientRing_map p g b)
  obtain ⟨q,hqlen,hq⟩ := relative_ramanujamPowerTuple_list p g hs hk
    n r hn hnu hspan hcard w hw
  refine ⟨l++q,?_,?_⟩
  · have hlen' : (l++q).length≤4*(n*p^r)*((r+1)*(p^r+1)+1) := by
      rw [List.length_append]
      nlinarith
    exact hlen'.trans_lt (ramanujam_large_degree_natural_count_lt p n r hp hn hm)
  · rw [localPowerListSum_append,hl,hq]
    exact he.symm

#print axioms large_residue_degree_power_list
end WaringSiegel.WSL4
