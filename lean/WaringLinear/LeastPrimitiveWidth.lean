import WaringLinear.LocalWidthGlobal
import WaringSiegel.WSL4PolynomialTarget

/-! # Existence of the least primitive width over all completed integer rings -/
noncomputable section
open WaringSiegel WaringSiegel.WSL4
open scoped NumberField BigOperators
namespace WaringLinear

theorem polynomial_primitive_width (K : Type) [Field K] [NumberField K] (k : ℕ) (hk : 3≤k) :
    PrimitiveWidthBound K k (8*k^5) := by
  intro v a ha
  letI := completionIntegers_isAdicComplete v
  letI := completionIntegers_residueFinite v
  have hsq := Thresholds.square_le_polynomial_local_bound k (by omega)
  have h2 : 2*k≤k^2 := by nlinarith
  by_cases prime : Nat.Prime k
  · exact power_tuple_with_unit_mono k (by omega) (odd_prime_power_tuple_adic k prime hk ha) (h2.trans hsq)
  by_cases wild : (k:𝓞 K)∈v.asIdeal
  · have hring := (WSL4Local.mem_powerGeneratedRing_iff k a).2 ha
    have hsub : a-1∈WSL4Local.powerGeneratedRing k _ :=
      (WSL4Local.powerGeneratedRing k _).sub_mem hring (WSL4Local.powerGeneratedRing k _).one_mem
    obtain ⟨l,hlen,hl⟩ := remainingLocalPowerClaim_verified K k hk prime v wild (a-1) hsub
    exact unit_power_tuple_of_short_list k (by omega) l (by omega) hl
  · letI := completionIntegers_henselianLocalRing v
    exact power_tuple_with_unit_mono k (by omega) (power_tuple_henselian_of_unit_of_finite_residue k
      (by omega) ((completion_nat_isUnit_iff k v).mpr wild) ha) (by omega)

def primitiveWidth (K : Type) [Field K] [NumberField K] (k : ℕ) (hk : 3≤k) : ℕ :=
  @Nat.find _ (Classical.decPred _) ⟨_,polynomial_primitive_width K k hk⟩

theorem primitiveWidth_spec (K : Type) [Field K] [NumberField K] (k : ℕ) (hk : 3≤k) :
    PrimitiveWidthBound K k (primitiveWidth K k hk) := by
  classical
  exact Nat.find_spec (show ∃ L, PrimitiveWidthBound K k L from ⟨_,polynomial_primitive_width K k hk⟩)

theorem primitiveWidth_le (K : Type) [Field K] [NumberField K] (k L : ℕ) (hk : 3≤k)
    (width : PrimitiveWidthBound K k L) : primitiveWidth K k hk≤L := by
  classical
  exact Nat.find_min' (show ∃ L, PrimitiveWidthBound K k L from ⟨_,polynomial_primitive_width K k hk⟩) width

#print axioms polynomial_primitive_width
#print axioms primitiveWidth_spec
#print axioms primitiveWidth_le
end WaringLinear
