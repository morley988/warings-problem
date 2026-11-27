import WaringLinear.MarkedStageScale
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Explicit constants for the high-conductor slack and the dyadic Gram logarithm -/
noncomputable section
namespace WaringLinear

/-- The threshold on which an off-diagonal correlation E X^(1−σ) is
absorbed by twice the large-value cutoff. The threshold is explicit. -/
theorem gram_slack_threshold (E σ z X : ℝ) (hE : 0<E) (hδ : 2*z<σ)
    (hX : (32*E)^(1/(σ-2*z))≤X) : 32*E≤X^(σ-2*z) := by
  have δ : 0<σ-2*z := by linarith
  have b : 0<32*E := by positivity
  have h := Real.rpow_le_rpow (Real.rpow_nonneg b.le _) hX δ.le
  rwa [←Real.rpow_mul b.le,div_mul_cancel₀ _ δ.ne',Real.rpow_one] at h

/-- The explicit finite-Gram constant is at most K X^ε for every X≥1.
K is uniform over the entire family of nodes and cutoffs. -/
theorem gram_log_loss (X z ε : ℝ) (hX:1≤X) (hz:0≤z) (hε:0<ε) :
    18+8*z*Real.logb 2 X ≤ (18+8*z/(ε*Real.log 2))*X^ε := by
  have x0 : 0<X := zero_lt_one.trans_le hX
  have b := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos x0 ε)
  rw [Real.log_rpow x0] at b
  have ℓ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ht : 1≤X^ε := Real.one_le_rpow hX hε.le
  have u : Real.logb 2 X≤X^ε/(ε*Real.log 2) := by
    rw [Real.logb]
    apply (div_le_div_iff₀ ℓ (mul_pos hε ℓ)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right b ℓ.le,ℓ.le]
  have v := mul_le_mul_of_nonneg_left u (show 0≤8*z by positivity)
  calc
    _ ≤ 18*X^ε+(8*z)*(X^ε/(ε*Real.log 2)) := by linarith
    _ = _ := by ring

/-- An ordinary prior-order P^ε loss and one amplitude logarithm give
P^(2ε). In the unchanged-order branch the existing P^(2ε) remains fixed,
so induction on the finite number of marks accumulates constants alone. -/
theorem gram_state_budget (I X P r z ε L U V W : ℝ)
    (hI : I ≤ (L*P^ε + U*(18+8*z*Real.logb 2 X)*P^ε + V*W*P^(2*ε))*X^r)
    (hX:1≤X) (hXP:X≤P) (hz:0≤z) (hε:0<ε) (hL:0≤L) (hU:0≤U) :
    I≤(L+U*(18+8*z/(ε*Real.log 2))+V*W)*P^(2*ε)*X^r := by
  let C := 18+8*z/(ε*Real.log 2)
  have p1 : 1≤P := hX.trans hXP
  have pp : 0<P := zero_lt_one.trans_le p1
  have xx : 0<X := zero_lt_one.trans_le hX
  have C0 : 0≤C := by dsimp [C]; positivity
  have log := (gram_log_loss X z ε hX hz hε).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow xx.le hXP hε.le) C0)
  have hlog := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left log hU) (Real.rpow_nonneg pp.le ε)
  have e : P^ε*P^ε=P^(2*ε) := by rw [←Real.rpow_add pp]; congr 1; ring
  have pe : P^ε≤P^(2*ε) := Real.rpow_le_rpow_of_exponent_le p1 (by linarith)
  apply hI.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg xx.le _)
  change _≤(L+U*C+V*W)*P^(2*ε)
  nlinarith only [hlog,mul_le_mul_of_nonneg_left pe hL,
    congrArg (fun t:ℝ => U*C*t) e]

#print axioms gram_state_budget
end WaringLinear
