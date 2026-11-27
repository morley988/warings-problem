import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000

theorem triangle_card_le_nat_sum (s : Finset ℕ) :
    s.card*(s.card-1)/2 ≤ ∑ i∈s,i := by
  induction s using Finset.induction_on_max with
  | h0 => simp
  | @step a s has ih =>
    have ha : a∉s := by intro h; exact (has a h).false
    have hcard : s.card≤a := by
      calc s.card≤(Finset.range a).card := Finset.card_mono (by
            intro i hi; exact Finset.mem_range.mpr (has i hi))
           _ = a := Finset.card_range a
    rw [Finset.card_insert_of_notMem ha,Finset.sum_insert ha,Nat.triangle_succ]
    omega

theorem nat_sum_le_triangle_add (s : Finset ℕ) (n : ℕ) (hs : ∀i∈s,i≤n) :
    (∑ i∈s,i)≤s.card*(s.card-1)/2+s.card*(n+1-s.card) := by
  have hcard : s.card≤n+1 := by
    calc s.card≤(Finset.range (n+1)).card := Finset.card_mono (by
          intro i hi; exact Finset.mem_range.mpr (by have := hs i hi; omega))
         _ = n+1 := Finset.card_range _
  let r := s.image (fun i => n-i)
  have hinj : Set.InjOn (fun i : ℕ => n-i) s := by
    intro i hi j hj he
    change n-i=n-j at he
    have := hs i hi
    have := hs j hj
    omega
  have hrcard : r.card=s.card := Finset.card_image_of_injOn hinj
  have he : (∑ i∈r,i)+(∑ i∈s,i)=s.card*n := by
    rw [Finset.sum_image hinj,← Finset.sum_add_distrib]
    calc
      (∑i∈s,(n-i+i))=∑ _i∈s,n := by
        exact Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hs i hi))
      _ = _ := by simp
  have hl := triangle_card_le_nat_sum r
  rw [hrcard] at hl
  have ht : (s.card*(s.card-1)/2)*2=s.card*(s.card-1) := by
    simpa only [Finset.sum_range_id] using Finset.sum_range_id_mul_two s.card
  by_cases hzero : s.card=0
  · have he0 : s=∅ := Finset.card_eq_zero.mp hzero
    simp [he0]
  · have hpred : s.card-1+1=s.card := Nat.sub_add_cancel (by omega)
    have hsub : n+1-s.card+s.card=n+1 := Nat.sub_add_cancel hcard
    nlinarith
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.triangle_card_le_nat_sum
#print axioms WaringSiegel.WSL4Weil.nat_sum_le_triangle_add
