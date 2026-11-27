import Waring.BasicMatching
import Waring.HeightMeasurability

/-!
# Literal auxiliary major arcs and intrinsic height

The original denominator/error definition is retained. The major arcs are
proved to lie in the intrinsic-height sublevel P, including the positive
power of the smoothness cutoff in the original error denominator.
-/

noncomputable section
namespace Waring.AuxiliaryMajorArcs
open Waring.RationalHeight Waring.BasicMatching

def MajorAtCutoff (P X α : ℝ) : Prop :=
  ∃ r : ℚ, (r.den:ℝ) ≤ P ∧ error α r ≤ 1/X

theorem major_iff_not_minor (P X α : ℝ) :
    MajorAtCutoff P X α ↔ ¬MinorAtCutoff P X α := by
  classical
  unfold MajorAtCutoff MinorAtCutoff
  push_neg
  constructor <;> rintro ⟨r,h1,h2⟩ <;> exact ⟨r,h2,h1⟩

theorem measurableSet_major (P X : ℝ) : MeasurableSet {α | MajorAtCutoff P X α} := by
  classical
  have heq : {α | MajorAtCutoff P X α} =
      ⋃ r : ℚ, {α : ℝ | (r.den:ℝ) ≤ P ∧ error α r ≤ 1/X} := by
    ext α
    simp only [MajorAtCutoff, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro r
  have herror : Measurable (fun α : ℝ => error α r) := by
    unfold error
    fun_prop
  by_cases hr : (r.den:ℝ) ≤ P
  · simpa only [hr, true_and] using measurableSet_le herror (measurable_const (a := 1/X))
  · simp only [hr, false_and, Set.setOf_false, MeasurableSet.empty]

theorem major_height_upper {P X V α : ℝ} (hmajor : MajorAtCutoff P X α)
    (hV : 0 ≤ V) (hX : 0 < X) (hVX : V/X ≤ P) : height V α ≤ P := by
  obtain ⟨r,hr,herr⟩ := hmajor
  apply (height_le_cost V α r).trans
  apply max_le hr
  have hh := mul_le_mul_of_nonneg_left herr hV
  exact (show V*error α r ≤ V/X by simpa only [mul_one_div] using hh).trans hVX

/-- Exact source error cutoff X=(V/P)R^rho; no R factor is dropped. -/
theorem source_major_height_upper {P V R rho α : ℝ}
    (hP : 0 < P) (hV : 0 < V) (hR : 1 ≤ R) (hrho : 0 ≤ rho)
    (hmajor : MajorAtCutoff P ((V/P)*R^rho) α) : height V α ≤ P := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hX : 0 < (V/P)*R^rho := by positivity
  apply major_height_upper hmajor hV.le hX
  apply (div_le_iff₀ hX).mpr
  have hrpow := Real.one_le_rpow hR hrho
  have hm := mul_le_mul_of_nonneg_left hrpow hV.le
  have heq : P*((V/P)*R^rho)=V*R^rho := by field_simp
  rw [heq]
  simpa only [mul_one] using hm

/-- The major-arc pointwise approximant denominator can be weakened to
the intrinsic height before applying the proved sublevel integration. -/
theorem source_weight_le_height {V α θ : ℝ} (hV : 0 ≤ V) (hθ : 0 ≤ θ) (r : ℚ) :
    (sumCost V α r)^(-θ) ≤ (height V α)^(-θ) := by
  apply Real.rpow_le_rpow_of_exponent_nonpos (height_pos V α) _ (neg_nonpos.mpr hθ)
  exact (height_le_cost V α r).trans (max_sum_cost_comparison hV α r).1

#print axioms source_major_height_upper
#print axioms source_weight_le_height

end Waring.AuxiliaryMajorArcs
