import Waring.IntegerDifferenceDegree
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial-size derivative values for the actual source phases

Differentiation commutes with every exact normalized centered difference.
The triangle inequality then bounds the derivative using the total shift
radius. Integer nonzero coefficients have absolute value at least one,
so the normalizing denominators never enlarge this estimate.
-/

noncomputable section
namespace Waring.IntegerDifferencePolynomial
open Polynomial

theorem derivative_difference (k : ℕ) (h m : ℤ) (p : Polynomial ℤ) (hm : m ≠ 0) :
    (difference k h m p).derivative = difference k h m p.derivative := by
  have hC : C (m^k) ≠ (0 : Polynomial ℤ) := by
    exact Polynomial.C_ne_zero.mpr (pow_ne_zero k hm)
  apply mul_left_cancel₀ hC
  rw [difference_mul]
  have H := congrArg Polynomial.derivative (difference_mul k h m p)
  simpa only [Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add,
    Polynomial.derivative_sub,Polynomial.derivative_comp,Polynomial.derivative_add,
    Polynomial.derivative_X,add_zero,sub_zero,one_mul] using H

def shiftRadius (k : ℕ) (params : List (ℤ × ℤ)) : ℝ :=
  (params.map (fun hm => |(hm.1 : ℝ)| * |(hm.2 : ℝ)|^k)).sum

theorem shiftRadius_nonneg (k : ℕ) (params : List (ℤ × ℤ)) :
    0 ≤ shiftRadius k params := by
  unfold shiftRadius
  apply List.sum_nonneg
  intro x hx
  obtain ⟨hm,hhm,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)

/-- Explicit size estimate at every real center, before specializing scales. -/
theorem derivative_eval_bound (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (z : ℝ) :
    |(powerPolynomial k params).derivative.eval₂ (Int.castRingHom ℝ) z| ≤
      (2 : ℝ)^params.length*(k : ℝ)*(|z|+shiftRadius k params)^(k-1) := by
  induction params generalizing z with
  | nil =>
    simp [powerPolynomial,Polynomial.derivative_X_pow,shiftRadius,abs_mul,abs_pow]
  | cons p rest ih =>
    have hm0 := hm p (List.mem_cons_self ..)
    have hmrest : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    rw [powerPolynomial,derivative_difference k p.1 p.2 _ hm0,
      difference_eval_real k p.1 p.2 _ hm0]
    have hmabs : 1 ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    have hden : 1 ≤ |(p.2 : ℝ)^k| := by
      rw [abs_pow]
      exact one_le_pow₀ hmabs
    have hrad := shiftRadius_nonneg k rest
    have hpRadius : shiftRadius k (p::rest) =
        |(p.1 : ℝ)| * |(p.2 : ℝ)|^k+shiftRadius k rest := rfl
    have hplus : |z+(p.1 : ℝ)*(p.2 : ℝ)^k|+shiftRadius k rest ≤
        |z|+shiftRadius k (p::rest) := by
      rw [hpRadius]
      have h := abs_add_le z ((p.1 : ℝ)*(p.2 : ℝ)^k)
      rw [abs_mul,abs_pow] at h
      linarith
    have hminus : |z-(p.1 : ℝ)*(p.2 : ℝ)^k|+shiftRadius k rest ≤
        |z|+shiftRadius k (p::rest) := by
      rw [hpRadius]
      have h := abs_sub z ((p.1 : ℝ)*(p.2 : ℝ)^k)
      rw [abs_mul,abs_pow] at h
      linarith
    have hbplus := (ih hmrest (z+(p.1 : ℝ)*(p.2 : ℝ)^k)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) hrad) hplus (k-1)) (by positivity))
    have hbminus := (ih hmrest (z-(p.1 : ℝ)*(p.2 : ℝ)^k)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) hrad) hminus (k-1)) (by positivity))
    rw [abs_div]
    calc
      _ ≤ |(powerPolynomial k rest).derivative.eval₂ (Int.castRingHom ℝ)
            (z+(p.1 : ℝ)*(p.2 : ℝ)^k) -
          (powerPolynomial k rest).derivative.eval₂ (Int.castRingHom ℝ)
            (z-(p.1 : ℝ)*(p.2 : ℝ)^k)| := div_le_self (abs_nonneg _) hden
      _ ≤ |(powerPolynomial k rest).derivative.eval₂ (Int.castRingHom ℝ)
            (z+(p.1 : ℝ)*(p.2 : ℝ)^k)| +
          |(powerPolynomial k rest).derivative.eval₂ (Int.castRingHom ℝ)
            (z-(p.1 : ℝ)*(p.2 : ℝ)^k)| := abs_sub _ _
      _ ≤ 2*((2 : ℝ)^rest.length*(k : ℝ)*(|z|+shiftRadius k (p::rest))^(k-1)) := by
        linarith [hbplus,hbminus]
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

theorem shiftRadius_le_box (k : ℕ) (params : List (ℤ × ℤ)) {P : ℝ}
    (hP : 0 ≤ P) (hbox : ∀ p ∈ params, |(p.1 : ℝ)| ≤ P ∧ |(p.2 : ℝ)| ≤ P) :
    shiftRadius k params ≤ (params.length : ℝ)*P^(k+1) := by
  induction params with
  | nil => simp [shiftRadius]
  | cons p rest ih =>
    have hprest := ih (fun q hq => hbox q (List.mem_cons_of_mem _ hq))
    have hp := hbox p (List.mem_cons_self ..)
    have hterm : |(p.1 : ℝ)| * |(p.2 : ℝ)|^k ≤ P^(k+1) := by
      calc
        _ ≤ P*P^k := mul_le_mul hp.1
          (pow_le_pow_left₀ (abs_nonneg _) hp.2 k) (pow_nonneg (abs_nonneg _) k) hP
        _ = P^(k+1) := by rw [pow_succ]; ring
    change |(p.1 : ℝ)| * |(p.2 : ℝ)|^k+shiftRadius k rest ≤ _
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- A fixed constant and fixed power work uniformly over the entire parameter box. -/
theorem derivative_eval_box_bound (k J : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (params : List (ℤ × ℤ)) (hlen : params.length ≤ J)
    (hm : ∀ p ∈ params, p.2 ≠ 0)
    (hbox : ∀ p ∈ params, |(p.1 : ℝ)| ≤ P ∧ |(p.2 : ℝ)| ≤ P)
    (z : ℝ) (hz : |z| ≤ P) :
    |(powerPolynomial k params).derivative.eval₂ (Int.castRingHom ℝ) z| ≤
      ((2 : ℝ)^J*(k : ℝ)*((J : ℝ)+1)^(k-1))*P^((k+1)*(k-1)) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hpow : P ≤ P^(k+1) := by
    simpa only [pow_succ,one_mul] using
      mul_le_mul_of_nonneg_right (one_le_pow₀ (n := k) hP) hP0
  have hlenR : (params.length : ℝ) ≤ J := by exact_mod_cast hlen
  have hradius : |z|+shiftRadius k params ≤ ((J : ℝ)+1)*P^(k+1) := by
    have hr := shiftRadius_le_box k params hP0 hbox
    have hmul := mul_le_mul_of_nonneg_right hlenR (pow_nonneg hP0 (k+1))
    nlinarith
  have hcount : (2 : ℝ)^params.length*(k : ℝ) ≤ (2 : ℝ)^J*(k : ℝ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) (Nat.cast_nonneg _)
  calc
    _ ≤ (2 : ℝ)^params.length*(k : ℝ)*(|z|+shiftRadius k params)^(k-1) :=
      derivative_eval_bound k params hm z
    _ ≤ (2 : ℝ)^J*(k : ℝ)*(((J : ℝ)+1)*P^(k+1))^(k-1) :=
      mul_le_mul hcount
        (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (shiftRadius_nonneg k params)) hradius (k-1))
        (pow_nonneg (add_nonneg (abs_nonneg _) (shiftRadius_nonneg k params)) _)
        (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    _ = _ := by rw [mul_pow,← pow_mul]; ring

/-- At a fixed sufficiently large ambient scale the derivative magnitude is
bounded by a pure power, exactly as required by the bad-factor theorem. -/
theorem derivative_magnitude_polynomial_bound (k J : ℕ) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ params : List (ℤ × ℤ), params.length ≤ J →
      (∀ p ∈ params, p.2 ≠ 0) →
      (∀ p ∈ params, |(p.1 : ℝ)| ≤ P ∧ |(p.2 : ℝ)| ≤ P) →
      ∀ z : ℤ, |(z : ℝ)| ≤ P →
      (((powerPolynomial k params).derivative.eval z).natAbs : ℝ) ≤
        P^(((k+1)*(k-1)+1 : ℕ) : ℝ) := by
  let C : ℝ := (2 : ℝ)^J*(k : ℝ)*((J : ℝ)+1)^(k-1)
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro P hPP₀ params hlen hm hbox z hz
  have hP : 1 ≤ P := (le_max_left _ _).trans hPP₀
  have hCP : C ≤ P := (le_max_right _ _).trans hPP₀
  have heval := Polynomial.eval₂_at_apply (p := (powerPolynomial k params).derivative)
    (Int.castRingHom ℝ) z
  change (powerPolynomial k params).derivative.eval₂ (Int.castRingHom ℝ) (z : ℝ) =
    (((powerPolynomial k params).derivative.eval z : ℤ) : ℝ) at heval
  have habs : (((powerPolynomial k params).derivative.eval z).natAbs : ℝ) =
      |(powerPolynomial k params).derivative.eval₂ (Int.castRingHom ℝ) (z : ℝ)| := by
    rw [heval,Nat.cast_natAbs,Int.cast_abs]
  rw [habs,Real.rpow_natCast]
  calc
    _ ≤ C*P^((k+1)*(k-1)) := derivative_eval_box_bound k J hP params hlen hm hbox (z : ℝ) hz
    _ ≤ P*P^((k+1)*(k-1)) :=
      mul_le_mul_of_nonneg_right hCP (pow_nonneg (zero_le_one.trans hP) _)
    _ = P^((k+1)*(k-1)+1) := by rw [pow_succ]; ring

#print axioms derivative_difference
#print axioms derivative_eval_bound
#print axioms derivative_magnitude_polynomial_bound
end Waring.IntegerDifferencePolynomial
