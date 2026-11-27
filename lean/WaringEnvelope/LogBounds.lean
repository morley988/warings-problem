import WaringEnvelope.Check
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Soundness of the elementary logarithm enclosures in the menus -/
noncomputable section
open scoped BigOperators
open Finset Nat
set_option maxRecDepth 32768
namespace WaringEnvelope

private def horner (x : ℝ) : ℕ → ℝ → ℝ
  | 0, v => v
  | i+1, v => horner x i (1+x*v/(i+1 : ℝ))

private theorem horner_mono {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Monotone (horner x n) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih =>
    intro a b hab
    apply ih
    exact add_le_add_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab hx)
      (by positivity)) _

private theorem horner_series (x : ℝ) (n : ℕ) (v : ℝ) :
    horner x n v = (∑ i ∈ range n, x^i / (i.factorial : ℝ)) + x^n/(n.factorial : ℝ)*v := by
  induction n generalizing v with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner,ih,sum_range_succ,Nat.factorial_succ,pow_succ]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring

private theorem horner_floor_step (d h n v : ℕ) (hd : 0 < d) :
    ((d + h*v/(d*(n+1)) : ℕ) : ℝ)/d ≤
      1 + ((h:ℝ)/d)*((v:ℝ)/d)/((n:ℝ)+1) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hf : ((h*v/(d*(n+1)) : ℕ) : ℝ) ≤ (h:ℝ)*v/(d*((n:ℝ)+1)) := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      (Nat.cast_div_le (α := ℝ) (m := h*v) (n := d*(n+1)))
  push_cast
  calc
    _ ≤ ((d:ℝ) + (h:ℝ)*v/(d*((n:ℝ)+1)))/d :=
      div_le_div_of_nonneg_right (add_le_add_left hf _) hd'.le
    _ = _ := by field_simp

private theorem dpos : 0<D := by decide
attribute [local irreducible] D

private theorem expLoop_le_horner (d h n v : ℕ) (hd : 0<d) :
    (expLoopScale d h n v : ℝ)/d ≤ horner ((h:ℝ)/d) n ((v:ℝ)/d) := by
  induction n generalizing v with
  | zero => exact le_rfl
  | succ n ih =>
    change (expLoopScale d h n (d + h*v/(d*(n+1))) : ℝ)/d ≤
      horner ((h:ℝ)/d) n (1 + ((h:ℝ)/d)*((v:ℝ)/d)/((n:ℝ)+1))
    exact (ih _).trans (horner_mono (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) n
      (horner_floor_step d h n v hd))

/-- The floor-Horner exponential minorant works at any positive denominator and
any truncation order. -/
theorem expLoopScale_le_exp (d h n : ℕ) (hd : 0<d) :
    (expLoopScale d h n d:ℝ)/d ≤ Real.exp ((h:ℝ)/d) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  calc
    _ ≤ horner ((h:ℝ)/d) n ((d:ℝ)/d) := expLoop_le_horner d h n d hd
    _ = ∑ i ∈ range (n+1), ((h:ℝ)/d)^i/(i.factorial : ℝ) := by
      rw [horner_series,div_self hd'.ne',mul_one,Finset.sum_range_succ (n := n)]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by positivity) _

/-- Every positive logarithm admitted by the integer checker has the stated
real upper bound. This covers the base, all 54 large endpoints, the cap and
the infinite-branch plateau. -/
theorem validLog_sound (p q h : ℕ) (hv : validLog p q h = true) :
    Real.log ((p:ℝ)/q) ≤ (h:ℝ)/D := by
  simp only [validLog,Bool.and_eq_true,decide_eq_true_eq] at hv
  obtain ⟨⟨hq,hp⟩,hcert⟩ := hv
  have hD : (0:ℝ) < D := by exact_mod_cast dpos
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  apply (Real.log_le_iff_le_exp (div_pos hp' hq')).mpr
  calc
    _ ≤ (expLoop h 120 D : ℝ)/D := by
      rw [div_le_div_iff₀ hq' hD]
      exact_mod_cast hcert.trans_eq (Nat.mul_comm _ _)
    _ ≤ horner ((h:ℝ)/D) 120 ((D:ℝ)/D) := expLoop_le_horner D h 120 D dpos
    _ = ∑ i ∈ range (120+1), ((h:ℝ)/D)^i/(i.factorial : ℝ) := by
      rw [horner_series,div_self hD.ne',mul_one,Finset.sum_range_succ (n := 120)]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by positivity) _

/-- The logarithmic trapezoid bound used for all steps, without a restriction
on the ratio of consecutive heights. -/
theorem twice_log_le_sub_inv (x : ℝ) (hx : 1 ≤ x) :
    2*Real.log x ≤ x-x⁻¹ := by
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hx)
  rw [Real.sinh_eq,Real.exp_log (zero_lt_one.trans_le hx),Real.exp_neg,
    Real.exp_log (zero_lt_one.trans_le hx)] at h
  linarith

#print axioms expLoopScale_le_exp
#print axioms validLog_sound
#print axioms twice_log_le_sub_inv
end WaringEnvelope
