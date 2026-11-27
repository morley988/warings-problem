import Waring.RationalHeightMin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurability of the actual intrinsic rational height -/

noncomputable section
namespace Waring.RationalHeight

theorem continuous_cost (V : ℝ) (r : ℚ) : Continuous (fun α : ℝ => cost V α r) := by
  unfold cost
  fun_prop

theorem height_lt_iff {V α y : ℝ} (hV : 0 < V) :
    height V α < y ↔ ∃ r : ℚ, cost V α r < y := by
  constructor
  · intro hy
    obtain ⟨r,hr⟩ := exists_minimizer hV α
    exact ⟨r, hr ▸ hy⟩
  · rintro ⟨r,hr⟩
    exact (height_le_cost V α r).trans_lt hr

theorem measurable_height {V : ℝ} (hV : 0 < V) : Measurable (height V) := by
  apply measurable_of_Iio
  intro y
  have heq : (height V) ⁻¹' Set.Iio y = ⋃ r : ℚ, {α : ℝ | cost V α r < y} := by
    ext α
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq]
    exact height_lt_iff hV
  rw [heq]
  exact MeasurableSet.iUnion (fun r => measurableSet_lt (continuous_cost V r).measurable measurable_const)

theorem measurableSet_height_le {V Z : ℝ} (hV : 0 < V) :
    MeasurableSet {α : ℝ | height V α ≤ Z} :=
  measurableSet_le (measurable_height hV) measurable_const

theorem measurableSet_height_shell {V A B : ℝ} (hV : 0 < V) :
    MeasurableSet {α : ℝ | A ≤ height V α ∧ height V α ≤ B} :=
  (measurableSet_le measurable_const (measurable_height hV)).inter (measurableSet_height_le hV)

#print axioms measurable_height

end Waring.RationalHeight
