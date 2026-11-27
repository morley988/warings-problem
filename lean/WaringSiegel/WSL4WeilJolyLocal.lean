import WaringSiegel.WSL4WeilJolyIntegral
import WaringSiegel.WSL4WeilJolyFrobenius
import WaringSiegel.WSL4WeilJolyLists
import WaringSiegel.WSL4ArchLocalAffine

noncomputable section
open Polynomial IsLocalRing
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000

/-- Joly's short representation in residue characteristic equal to the odd prime exponent. -/
theorem eligible_odd_prime_power_list_bad_characteristic
    {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (k : ℕ) [Fact k.Prime] (hk : 2<k) [CharP (ResidueField A) k]
    (a : A) (ha : a∈AddSubgroup.closure (Set.range (fun x : A => x^k))) :
    ∃ l : List A, l.length≤2*k-1 ∧ WSL4.localPowerListSum k l=a := by
  obtain ⟨x,z,hxz⟩ := eligible_eq_power_add_prime_mul k a ha
  obtain ⟨F,c,hF,hmap⟩ := exists_joly_integral_polynomial k hk
  obtain ⟨t,ht⟩ := WSL4.integer_polynomial_surjective_of_affine_mod_prime k F c hmap z
  have hodd : Odd k := (Fact.out : k.Prime).odd_of_ne_two (by omega)
  obtain ⟨l,hlen,hl⟩ := jolyNumerator_power_list k hodd t
  refine ⟨x::l,by simp only [List.length_cons,hlen]; omega,?_⟩
  rw [WSL4.localPowerListSum_cons,hl,hF,eval₂_mul,eval₂_C,ht]
  simpa only [Int.coe_castRingHom,Int.cast_natCast] using hxz.symm
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.eligible_odd_prime_power_list_bad_characteristic
