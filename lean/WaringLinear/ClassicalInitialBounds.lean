import WaringLinear.RationalTransfer
import WaringSiegel.WSL4EightCubesTarget
import Mathlib.NumberTheory.SumFourSquares

/-! The first three unconditional positive-root Waring bounds. -/
noncomputable section
open Finset
open scoped Classical BigOperators
namespace WaringLinear.ClassicalInitialBounds

/-- Removing zero coordinates permits Lagrange's four natural squares to be
read directly in the positive-root Waring predicate. -/
theorem positive_of_nonnegative {k s n : ℕ} (hk : k ≠ 0) (x : Fin s → ℕ)
    (hx : ∑ i,x i ^ k = n) : Waring.RepresentableByAtMost k s n := by
  let S := univ.filter (fun i => x i ≠ 0)
  let e := S.equivFin.symm
  refine ⟨S.card,by simpa using card_le_univ S,fun j=>x (e j).1,?_,?_⟩
  · intro j
    exact Nat.pos_of_ne_zero (mem_filter.mp (e j).2).2
  · calc
      (∑ j,x (e j).1 ^ k) = ∑ i:S,x i.1 ^ k := e.sum_comp (fun i:S=>x i.1^k)
      _ = ∑ i∈S,x i^k := sum_coe_sort S (fun i => x i^k)
      _ = ∑ i,x i^k := by
        apply sum_subset (subset_univ _)
        intro i _ hi
        have hz : x i = 0 := by simpa [S] using hi
        simp [hz,hk]
      _ = n := hx

theorem one_power : Waring.WaringBound 1 1 := by
  refine ⟨1,fun n hn=>⟨1,le_rfl,fun _ => n,fun _ => hn,?_⟩⟩
  simp

theorem four_squares : Waring.WaringBound 2 4 := by
  refine ⟨0,fun n _ => ?_⟩
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares n
  apply positive_of_nonnegative (by decide) ![a,b,c,d]
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem eight_cubes : Waring.WaringBound 3 8 :=
  WaringLinear.classical_of_rational_field 3 8 (by decide) (WaringSiegel.WSL4.eight_cubes_number_field ℚ)

#print axioms one_power
#print axioms four_squares
#print axioms eight_cubes
end WaringLinear.ClassicalInitialBounds
