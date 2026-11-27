import Waring.SeedCompletionCurveNoLine
import Waring.SeedCompletionCurveFactors

/-! # Coordinate degrees and unit leading coefficient of the source curve -/

noncomputable section
open Polynomial
open scoped Polynomial Polynomial.Bivariate
namespace Waring.SeedCompletionCurveTranslation
open SeedCompletionCurveFactors

theorem separatedCurve_natDegree (f : ℝ[X]) {g : ℝ[X]} (hg : 0 < g.natDegree) :
    (separatedCurve f g).natDegree=g.natDegree := by
  have hlt : (C f : ℝ[X][Y]).natDegree < (g.map C).natDegree := by
    rw [natDegree_C,natDegree_map_eq_of_injective C_injective]
    exact hg
  rw [separatedCurve,natDegree_sub_eq_right_of_natDegree_lt hlt,
    natDegree_map_eq_of_injective C_injective]

theorem separatedCurve_leadingCoeff (f : ℝ[X]) {g : ℝ[X]} (hg : 0 < g.natDegree) :
    (separatedCurve f g).leadingCoeff= -C g.leadingCoeff := by
  have hlt : (C f : ℝ[X][Y]).natDegree < (g.map C).natDegree := by
    rw [natDegree_C,natDegree_map_eq_of_injective C_injective]
    exact hg
  rw [separatedCurve,leadingCoeff_sub_of_degree_lt' (degree_lt_degree hlt),
    leadingCoeff_map' C_injective]

theorem separatedCurve_leadingCoeff_isUnit (f : ℝ[X]) {g : ℝ[X]} (hg : 0 < g.natDegree) :
    IsUnit (separatedCurve f g).leadingCoeff := by
  rw [separatedCurve_leadingCoeff f hg]
  exact (isUnit_C.mpr (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hg)).isUnit).neg

theorem swap_separatedCurve (f g : ℝ[X]) :
    Bivariate.swap (separatedCurve f g)= -separatedCurve g f := by
  ext i j
  rw [coeff_coeff_swap]
  by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    simp [separatedCurve,coeff_C,coeff_map,hi,hj]

theorem separatedCurve_swap_natDegree {f : ℝ[X]} (g : ℝ[X]) (hf : 0 < f.natDegree) :
    (Bivariate.swap (separatedCurve f g)).natDegree=f.natDegree := by
  rw [swap_separatedCurve,natDegree_neg,separatedCurve_natDegree g hf]

#print axioms separatedCurve_leadingCoeff_isUnit
#print axioms separatedCurve_swap_natDegree
end Waring.SeedCompletionCurveTranslation
