import Waring.ShortHeightDistribution
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform absorption of fixed logarithmic losses

The estimates hold for every real P >= 1, with one finite positive constant
for each positive epsilon and each fixed natural power. They cover both the
explicit real logarithm and canonical binary dyadic depths. No eventual-growth
assumption is used in place of a proof.
-/

noncomputable section
namespace Waring.DyadicLogLoss

def logLoss (P : ℝ) : ℝ := 2 + Real.log P / Real.log 2

theorem logLoss_nonneg {P : ℝ} (hP : 1 ≤ P) : 0 ≤ logLoss P := by
  have hp := Real.log_nonneg hP
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  dsimp [logLoss]
  positivity

theorem logLoss_le_rpow {δ P : ℝ} (hδ : 0 < δ) (hP : 1 ≤ P) :
    logLoss P ≤ (2 + 1/(δ*Real.log 2))*P^δ := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 1 ≤ P^δ := Real.one_le_rpow hP hδ.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hP) hδ
  calc
    logLoss P ≤ 2*P^δ+(P^δ/δ)/Real.log 2 := by
      unfold logLoss
      exact add_le_add (by linarith) (div_le_div_of_nonneg_right hl h2.le)
    _ = (2+1/(δ*Real.log 2))*P^δ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Any fixed finite logarithmic power is uniformly bounded by an arbitrarily
small positive power of the real length parameter. -/
theorem logLoss_pow_le_rpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → (logLoss P)^m ≤ C*P^ε := by
  let δ : ℝ := ε / ((m : ℝ)+1)
  have hm : (0 : ℝ) < (m : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hm
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 2+1/(δ*Real.log 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hδm : δ*(m : ℝ) ≤ ε := by
    have hid : δ*((m : ℝ)+1) = ε := div_mul_cancel₀ ε hm.ne'
    nlinarith
  refine ⟨A^m, by positivity, ?_⟩
  intro P hP
  have hb := pow_le_pow_left₀ (logLoss_nonneg hP) (logLoss_le_rpow hδ hP) m
  calc
    (logLoss P)^m ≤ (A*P^δ)^m := hb
    _ = A^m*P^(δ*(m : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hP)]
    _ ≤ A^m*P^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP hδm) (by positivity)

/-- Convenient statement in the exact logarithmic notation used by Q1--Q5. -/
theorem explicit_log_pow_le_rpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      (2+Real.log P/Real.log 2)^m ≤ C*P^ε :=
  logLoss_pow_le_rpow m hε

/-- Every efficient dyadic cover has the same uniform power absorption. -/
theorem dyadic_depth_pow_le_rpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ T : ℕ,
      (2 : ℝ)^T ≤ 2*P → ((T+1 : ℕ) : ℝ)^m ≤ C*P^ε := by
  obtain ⟨C, hC, hbound⟩ := logLoss_pow_le_rpow m hε
  refine ⟨C, hC, ?_⟩
  intro P hP T hcover
  have hd : ((T+1 : ℕ) : ℝ) ≤ logLoss P :=
    ShortHeightDistribution.dyadic_depth_le_log (a := 1) T le_rfl
      (zero_lt_one.trans_le hP) (by simpa only [one_mul] using hcover)
  exact (pow_le_pow_left₀ (by positivity) hd m).trans (hbound P hP)

/-- The canonical binary ceiling logarithm always produces an efficient cover. -/
theorem pow_clog_le_twice (N : ℕ) (hN : 0 < N) :
    (2 : ℝ)^(Nat.clog 2 N) ≤ 2*(N : ℝ) := by
  by_cases hN1 : N = 1
  · subst N
    norm_num
  · have hN2 : 2 ≤ N := by omega
    have hpos := Nat.clog_pos (by norm_num : 1 < 2) hN2
    have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hN2
    have hsucc : (Nat.clog 2 N).pred+1 = Nat.clog 2 N := Nat.succ_pred_eq_of_pos hpos
    have hbound : 2^(Nat.clog 2 N) ≤ 2*N := by
      rw [← hsucc, pow_succ]
      nlinarith
    exact_mod_cast hbound

/-- Natural binary ceiling depths, without an unspecified choice of a cover. -/
theorem clog_depth_pow_le_rpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      ((Nat.clog 2 N+1 : ℕ) : ℝ)^m ≤ C*(N : ℝ)^ε := by
  obtain ⟨C, hC, hbound⟩ := dyadic_depth_pow_le_rpow m hε
  refine ⟨C, hC, ?_⟩
  intro N hN
  exact hbound N (by exact_mod_cast hN) _ (pow_clog_le_twice N hN)

/-- The second logarithmic factor used in the short-height bound is controlled
by twice the common logarithmic loss. -/
theorem doubled_log_le (P : ℝ) :
    2+2*Real.log P/Real.log 2 ≤ 2*logLoss P := by
  unfold logLoss
  ring_nf
  linarith

#print axioms logLoss_pow_le_rpow
#print axioms dyadic_depth_pow_le_rpow
#print axioms clog_depth_pow_le_rpow
end Waring.DyadicLogLoss
