import WaringSiegel.WSL4WeilVandermonde
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000

theorem sum_range_min_exact (n j : ℕ) (hj : j≤n) :
    (∑ i∈Finset.range n,min i j)=j*(j-1)/2+(n-j)*j := by
  rw [← Finset.sum_range_add_sum_Ico _ hj]
  have hl : (∑ i∈Finset.range j,min i j)=j*(j-1)/2 := by
    rw [← Finset.sum_range_id]
    apply Finset.sum_congr rfl
    intro i hi
    exact min_eq_left (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hr : (∑ i∈Finset.Ico j n,min i j)=(n-j)*j := by
    calc
      (∑ i∈Finset.Ico j n,min i j) = ∑ _i∈Finset.Ico j n,j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact min_eq_right (Finset.mem_Ico.mp hi).1
      _ = _ := by simp
  rw [hl,hr]

theorem sum_fin_erase_min_exact (n : ℕ) (j : Fin (n+1)) :
    (∑ i∈Finset.univ.erase j,min i.val j.val)=
      j.val*(j.val-1)/2+(n-j.val)*j.val := by
  have hs := Finset.sum_erase_add (s := Finset.univ)
    (f := fun i : Fin (n+1) => min i.val j.val) (Finset.mem_univ j)
  have ht : (∑ i : Fin (n+1),min i.val j.val)=
      j.val*(j.val-1)/2+(n+1-j.val)*j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => min i j.val)]
    exact sum_range_min_exact (n+1) j.val (Nat.le_of_lt j.isLt)
  dsimp only at hs
  rw [min_self,ht] at hs
  have he : n+1-j.val=(n-j.val)+1 := by omega
  rw [he,add_mul,one_mul] at hs
  omega

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Actual geometric nodes in a DVR are distinct, without a field assumption. -/
theorem uniformizer_geometric_nodes_injective {pi : R} (hpi : Irreducible pi)
    (d n : ℕ) (hd : 0<d) :
    Function.Injective (fun j : Fin (n+1) => pi^(d*j.val)) := by
  intro i j hij
  have he := congrArg (IsDiscreteValuationRing.addVal R) hij
  rw [hpi.addVal_pow,hpi.addVal_pow] at he
  have hnat : d*i.val=d*j.val := by exact_mod_cast he
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hd hnat)

theorem uniformizer_power_sub_valuation {pi : R} (hpi : Irreducible pi)
    {a b : ℕ} (hab : a≠b) :
    IsDiscreteValuationRing.addVal R (pi^a-pi^b)=(min a b : ℕ) := by
  rcases lt_or_gt_of_ne hab with h|h
  · rw [(IsDiscreteValuationRing.addVal R).map_sub_eq_of_lt_left
      (by rw [hpi.addVal_pow,hpi.addVal_pow]; exact_mod_cast h),
      hpi.addVal_pow,min_eq_left h.le]
  · rw [(IsDiscreteValuationRing.addVal R).map_sub_eq_of_lt_right
      (by rw [hpi.addVal_pow,hpi.addVal_pow]; exact_mod_cast h),
      hpi.addVal_pow,min_eq_right h.le]

def geometricNodeDenominator (pi : R) (d n : ℕ) (j : Fin (n+1)) : R :=
  ∏ i∈Finset.univ.erase j,(pi^(d*j.val)-pi^(d*i.val))

theorem geometricNodeDenominator_ne_zero {pi : R} (hpi : Irreducible pi)
    (d n : ℕ) (hd : 0<d) (j : Fin (n+1)) :
    geometricNodeDenominator pi d n j≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hi).1
    ((uniformizer_geometric_nodes_injective hpi d n hd he).symm)

theorem geometricNodeDenominator_valuation {pi : R} (hpi : Irreducible pi)
    (d n : ℕ) (hd : 0<d) (j : Fin (n+1)) :
    IsDiscreteValuationRing.addVal R (geometricNodeDenominator pi d n j)=
      (d*(j.val*(j.val-1)/2+(n-j.val)*j.val) : ℕ) := by
  have hprod (s : Finset (Fin (n+1))) :
      IsDiscreteValuationRing.addVal R (∏ i∈s,(pi^(d*j.val)-pi^(d*i.val)))=
      ∑ i∈s,IsDiscreteValuationRing.addVal R (pi^(d*j.val)-pi^(d*i.val)) := by
    induction s using Finset.induction_on with
    | empty => simp [IsDiscreteValuationRing.addVal_one]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,IsDiscreteValuationRing.addVal_mul,ih]
  rw [geometricNodeDenominator,hprod]
  calc
    (∑ i∈Finset.univ.erase j,IsDiscreteValuationRing.addVal R
        (pi^(d*j.val)-pi^(d*i.val))) =
        ∑ i∈Finset.univ.erase j,((d*min i.val j.val : ℕ) : ℕ∞) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : j.val≠i.val := by
        intro he
        exact (Finset.mem_erase.mp hi).1 (Fin.ext he.symm)
      have hmul : d*j.val≠d*i.val := by
        intro he
        exact hij (Nat.eq_of_mul_eq_mul_left hd he)
      rw [uniformizer_power_sub_valuation hpi hmul,← mul_min,min_comm]
    _ = ((d*(∑ i∈Finset.univ.erase j,min i.val j.val) : ℕ) : ℕ∞) := by
      simp only [Nat.cast_mul,Nat.cast_sum,Finset.mul_sum]
    _ = _ := by rw [sum_fin_erase_min_exact]
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.geometricNodeDenominator_valuation
#print axioms WaringSiegel.WSL4Weil.geometricNodeDenominator_ne_zero
