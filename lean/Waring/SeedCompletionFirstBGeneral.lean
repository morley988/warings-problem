import Waring.FirstStageUpdates

/-! # The general genuine first-stage B second-moment update -/

noncomputable section
namespace Waring.FirstStageTransport
open SmoothMoments

/-- A lower adjacent moment and a doubled terminal smooth moment give the
source B_(1,2s+2) endpoint, using the proved actual F1 second estimate. -/
theorem admissible_B_second {k s : ℕ} (hk : SupportedFirstDegree k) {lam mu φ : ℝ}
    (hlam : AdmissibleExponent k (2*(s+1)) lam)
    (hmu : AdmissibleExponent k (4*(s+1)) mu)
    (hlamBound : lam ≤ 2*(s : ℝ)+1) (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1)
    (hbalance : mu-2*lam ≤ ((k : ℝ)+mu+1-2*lam)*φ) :
    AdmissibleExponent k (2*(s+2)) (1+lam+(2*((s : ℝ)+1)-lam)*φ) := by
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk2R : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hφ1 : φ ≤ 1 := by nlinarith
  apply first_stage_admissible (s := s) (by omega : 0 < k)
    hlam hφ0 hφ1
    (crossExponent_second hk hφ0 hφk hmu)
  · nlinarith
  · rfl
  · nlinarith

theorem admissible_eight_B_supported {k : ℕ} (hk : SupportedFirstDegree k)
    {lam mu φ : ℝ} (hlam : AdmissibleExponent k 6 lam) (hmu : AdmissibleExponent k 12 mu)
    (hlam5 : lam ≤ 5) (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1)
    (hbalance : mu-2*lam ≤ ((k : ℝ)+mu+1-2*lam)*φ) :
    AdmissibleExponent k 8 (1+lam+(6-lam)*φ) := by
  convert admissible_B_second (s := 2) hk hlam hmu
    (by norm_num; exact hlam5) hφ0 hφk hbalance using 1 <;> norm_num

#print axioms admissible_B_second
#print axioms admissible_eight_B_supported
end Waring.FirstStageTransport
