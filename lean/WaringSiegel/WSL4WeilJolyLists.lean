import WaringSiegel.WSL4WeilJolyPolynomial
import WaringSiegel.WSL4ArchLocalPowerLists

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000

/-- The numerator is literally a sum of2(k−1) powers when k is odd. -/
theorem jolyNumerator_power_list
    {A : Type*} [CommRing A] (k : ℕ) [NeZero k] (hk : Odd k) (t : A) :
    ∃ l : List A, l.length=2*(k-1) ∧
      WSL4.localPowerListSum k l=(jolyNumerator k).eval₂ (Int.castRingHom A) t := by
  let s : Finset (ZMod k) := Finset.univ.erase 0
  let l : List A := s.toList.map (fun _ => t)++s.toList.map (fun a => (a.val:A)-t)
  have hcard : s.card=k-1 := by simp [s,ZMod.card]
  have hlen : l.length=2*(k-1) := by
    simp only [l,List.length_append,List.length_map,Finset.length_toList,hcard]
    omega
  refine ⟨l,hlen,?_⟩
  have he (a : ZMod k) : t^k+((a.val:A)-t)^k=t^k-(t-(a.val:A))^k := by
    rw [show (a.val:A)-t=-(t-(a.val:A)) by ring,hk.neg_pow]
    ring
  have hsum : (∑ a∈s,(t^k-(t-(a.val:A))^k))=
      ∑ a : ZMod k,(t^k-(t-(a.val:A))^k) := by
    apply Finset.sum_erase
    simp
  calc
    WSL4.localPowerListSum k l =
        ∑ a∈s,(t^k+((a.val:A)-t)^k) := by
      simp only [l,WSL4.localPowerListSum,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,Finset.sum_map_toList,Finset.sum_add_distrib]
    _ = ∑ a : ZMod k,(t^k-(t-(a.val:A))^k) := by simp_rw [he]; exact hsum
    _ = (jolyNumerator k).eval₂ (Int.castRingHom A) t := by
      simp only [jolyNumerator,eval₂_finset_sum,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,
        Int.coe_castRingHom,Int.cast_natCast]
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.jolyNumerator_power_list
