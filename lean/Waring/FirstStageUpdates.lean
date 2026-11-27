import Waring.FirstStageFourthCross

/-!
# Genuine first-stage A and B exponent updates

The inequalities on the extraction parameter are numerical conditions;
the smooth-moment conclusions follow from the actual proved source
recurrence, auxiliary estimates and terminal Holder inequalities.
-/

noncomputable section
namespace Waring.FirstStageTransport
open SmoothMoments

theorem admissible_six_B {k : ℕ} (hk : SupportedFirstDegree k) {mu φ : ℝ}
    (hmu : AdmissibleExponent k 8 mu) (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1)
    (hbalance : mu-4 ≤ ((k : ℝ)+mu-3)*φ) :
    AdmissibleExponent k 6 (3+2*φ) := by
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk2R : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hφ1 : φ ≤ 1 := by nlinarith
  apply first_stage_admissible (s := 1) (by omega : 0 < k)
    (FourthMomentSeed.admissibleExponent_four hk2) hφ0 hφ1
    (crossExponent_second (s := 2) hk hφ0 hφk hmu)
  · norm_num
    linarith
  · norm_num
  · norm_num
    nlinarith

theorem admissible_eight_A_ninth {lam mu φ : ℝ}
    (hlam : AdmissibleExponent 9 6 lam) (hmu : AdmissibleExponent 9 8 mu)
    (hlam5 : lam ≤ 5) (hφ0 : 0 ≤ φ) (hφ9 : φ*9 ≤ 1)
    (hbalance : 1+3*mu-4*lam ≤ (28+3*mu-4*lam)*φ) :
    AdmissibleExponent 9 8 (1+lam+(6-lam)*φ) := by
  have hφ1 : φ ≤ 1 := by linarith
  apply first_stage_admissible (s := 2) (by norm_num : 0 < (9 : ℕ))
    hlam hφ0 hφ1 (crossExponent_fourth_ninth hφ0 hφ9 hmu)
  · norm_num
    nlinarith
  · norm_num
  · norm_num
    nlinarith

#print axioms admissible_six_B
#print axioms admissible_eight_A_ninth
end Waring.FirstStageTransport
