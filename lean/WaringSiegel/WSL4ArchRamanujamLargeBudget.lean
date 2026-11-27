import WaringSiegel.WSL4RamanujamNumerical
import WaringSiegel.WSL4ArchFiniteFieldResidueDegree

/-! # The exact large-degree local list budget and residue-size hypotheses -/
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1400000

theorem large_residue_degree_node_card
    {F : Type*} [Field F] [Finite F]
    (p n r f : ℕ) (hp : p.Prime) (hn : 0<n)
    (hcard : Nat.card F=p^f) (hmf : n*p^r≤f) :
    p^r<Nat.card F := by
  have hPm : p^r≤n*p^r := by
    calc
      p^r=1*p^r := by ring
      _≤n*p^r := Nat.mul_le_mul_right _ (show 1≤n from hn)
  have hrf : r<f := (Nat.lt_pow_self hp.one_lt).trans_le (hPm.trans hmf)
  rw [hcard]
  exact Nat.pow_lt_pow_right hp.one_lt hrf

theorem large_residue_degree_tame_le
    (p n r f : ℕ) (hp : p.Prime) (hmf : n*p^r≤f) : n≤f := by
  have hnP : n≤n*p^r := by
    simpa only [mul_one] using Nat.mul_le_mul_left n (Nat.one_le_pow _ _ hp.pos)
  exact hnP.trans hmf

theorem ramanujam_large_degree_natural_count_lt
    (p n r : ℕ) (hp : p.Prime) (hn : 0<n) (hm : 2≤n*p^r) :
    4*(n*p^r)*((r+1)*(p^r+1)+1)<8*(n*p^r)^5 := by
  let m := n*p^r
  have hPm : p^r≤m := by
    calc
      p^r=1*p^r := by ring
      _≤n*p^r := Nat.mul_le_mul_right _ (show 1≤n from hn)
  have hrP : r+1≤p^r := Nat.succ_le_of_lt (Nat.lt_pow_self hp.one_lt)
  have hshape : (r+1)*(p^r+1)+1≤m^2+m+1 := by
    calc
      _≤(p^r)*(p^r+1)+1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hrP) 1
      _≤m*(m+1)+1 := Nat.add_le_add_right (Nat.mul_le_mul hPm (Nat.add_le_add_right hPm 1)) 1
      _=m^2+m+1 := by ring
  have hbound : 4*m*((r+1)*(p^r+1)+1)≤(m^2+m+1)*(4*m+1) := by
    calc
      _≤4*m*(m^2+m+1) := Nat.mul_le_mul_left _ hshape
      _≤(m^2+m+1)*(4*m+1) := by nlinarith
  have hstrict : (m^2+m+1)*(4*m+1)<8*m^5 := by
    exact_mod_cast WSL4Local.ramanujam_large_residue_count_lt (m:ℝ) (by exact_mod_cast hm)
  exact hbound.trans_lt hstrict

#print axioms large_residue_degree_node_card
#print axioms large_residue_degree_tame_le
#print axioms ramanujam_large_degree_natural_count_lt
end WaringSiegel.WSL4
