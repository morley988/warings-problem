import WaringSiegel.WSL4WeilGoodExponents

/-! # Numerical solution of the inhomogeneous cubic three-step recurrence -/
noncomputable section
namespace WaringSiegel.WSL4Weil

def cubicBadMajorantConstant (q C : ℝ) : ℝ := q^2+3*C*q

theorem cubicBadMajorantConstant_nonneg (q C : ℝ) (hq : 2≤q) (hC : 0≤C) :
    0≤cubicBadMajorantConstant q C := by unfold cubicBadMajorantConstant; positivity

theorem cubicBadMajorantConstant_leading (q C : ℝ) (hq : 2≤q) (hC : 0≤C) :
    4*C≤cubicBadMajorantConstant q C := by
  unfold cubicBadMajorantConstant
  nlinarith [sq_nonneg q]

theorem cubicBadMajorant_base (q C A : ℝ) (hq : 2≤q) (hC : 0≤C)
    (r : ℕ) (hr : r≤2) (hA : A≤q^r) :
    A+3*C*q^((r:ℝ)/2) ≤ cubicBadMajorantConstant q C*q^(2*(r:ℝ)/3) := by
  have hq1 : 1≤q := by linarith
  have hq0 : 0<q := by linarith
  have hpow : q^r≤q^2 := by
    rw [← Real.rpow_natCast q r,← Real.rpow_natCast q 2]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by exact_mod_cast hr)
  have hhalf : q^((r:ℝ)/2)≤q := by
    conv_rhs => rw [← Real.rpow_one q]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    have hr' : (r:ℝ)≤2 := by exact_mod_cast hr
    linarith
  have hlarge : 1≤q^(2*(r:ℝ)/3) := Real.one_le_rpow hq1 (by positivity)
  calc
    _ ≤ q^2+3*C*q := add_le_add (hA.trans hpow)
      (mul_le_mul_of_nonneg_left hhalf (by positivity))
    _ ≤ _ := by
      change cubicBadMajorantConstant q C≤_
      exact le_mul_of_one_le_right (cubicBadMajorantConstant_nonneg q C hq hC) hlarge

theorem cubicBadMajorant_unit_case (q C A : ℝ) (hq : 2≤q) (hC : 0≤C)
    (r : ℕ) (hA : A≤C*q^((r:ℝ)/2)) :
    A+3*C*q^((r:ℝ)/2) ≤ cubicBadMajorantConstant q C*q^(2*(r:ℝ)/3) := by
  have hq1 : 1≤q := by linarith
  have hpow : q^((r:ℝ)/2)≤q^(2*(r:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by have : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith)
  calc
    _ ≤ 4*C*q^((r:ℝ)/2) := by linarith
    _ ≤ cubicBadMajorantConstant q C*q^((r:ℝ)/2) :=
      mul_le_mul_of_nonneg_right (cubicBadMajorantConstant_leading q C hq hC) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (cubicBadMajorantConstant_nonneg q C hq hC)

theorem cubicBadMajorant_recursion (q C A B : ℝ) (hq : 2≤q) (hC : 0≤C)
    (n : ℕ) (hA : A≤C*q^(((n+3:ℕ):ℝ)/2)+q^2*B)
    (hB : B+3*C*q^((n:ℝ)/2)≤cubicBadMajorantConstant q C*q^(2*(n:ℝ)/3)) :
    A+3*C*q^(((n+3:ℕ):ℝ)/2)≤
      cubicBadMajorantConstant q C*q^(2*((n+3:ℕ):ℝ)/3) := by
  have hq0 : 0<q := by linarith
  have hs : (4/3:ℝ)≤Real.sqrt q := Real.le_sqrt_of_sq_le (by nlinarith)
  have hhalf : q^2*q^((n:ℝ)/2)=Real.sqrt q*q^(((n+3:ℕ):ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast q 2,← Real.rpow_add hq0,← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  have hmain : q^2*q^(2*(n:ℝ)/3)=q^(2*((n+3:ℕ):ℝ)/3) := by
    rw [← Real.rpow_natCast q 2,← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  have habsorb : 4*C*q^(((n+3:ℕ):ℝ)/2)≤q^2*(3*C*q^((n:ℝ)/2)) := by
    calc
      _ ≤ (3*C*Real.sqrt q)*q^(((n+3:ℕ):ℝ)/2) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = _ := by rw [mul_assoc,← hhalf]; ring
  calc
    _ ≤ q^2*(B+3*C*q^((n:ℝ)/2)) := by nlinarith
    _ ≤ q^2*(cubicBadMajorantConstant q C*q^(2*(n:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hB (sq_nonneg q)
    _ = _ := by rw [← mul_assoc,mul_comm (q^2),mul_assoc,hmain]
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.cubicBadMajorant_recursion
