import Waring.IntegerDifferenceSize

/-! # Polynomial-size bounds for every actual integer difference phase

These bounds use the literal recursive polynomial and exact nonzero integer
normalizations. They supply frequency-size conditions without an analytic
assumption, uniformly over bounded parameter boxes at every fixed depth.
-/

noncomputable section
namespace Waring.IntegerDifferencePolynomial
open Polynomial

/-- Explicit size estimate at every real center, before specializing scales. -/
theorem powerPolynomial_eval_bound (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (z : ℝ) :
    |(powerPolynomial k params).eval₂ (Int.castRingHom ℝ) z| ≤
      (2 : ℝ)^params.length*(|z|+shiftRadius k params)^k := by
  induction params generalizing z with
  | nil =>
    simp [powerPolynomial,shiftRadius,abs_pow]
  | cons p rest ih =>
    have hm0 := hm p (List.mem_cons_self ..)
    have hmrest : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    rw [powerPolynomial,difference_eval_real k p.1 p.2 _ hm0]
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
        (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) hrad) hplus k) (by positivity))
    have hbminus := (ih hmrest (z-(p.1 : ℝ)*(p.2 : ℝ)^k)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) hrad) hminus k) (by positivity))
    rw [abs_div]
    calc
      _ ≤ |(powerPolynomial k rest).eval₂ (Int.castRingHom ℝ)
            (z+(p.1 : ℝ)*(p.2 : ℝ)^k) -
          (powerPolynomial k rest).eval₂ (Int.castRingHom ℝ)
            (z-(p.1 : ℝ)*(p.2 : ℝ)^k)| := div_le_self (abs_nonneg _) hden
      _ ≤ |(powerPolynomial k rest).eval₂ (Int.castRingHom ℝ)
            (z+(p.1 : ℝ)*(p.2 : ℝ)^k)| +
          |(powerPolynomial k rest).eval₂ (Int.castRingHom ℝ)
            (z-(p.1 : ℝ)*(p.2 : ℝ)^k)| := abs_sub _ _
      _ ≤ 2*((2 : ℝ)^rest.length*(|z|+shiftRadius k (p::rest))^k) := by
        linarith [hbplus,hbminus]
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

/-- A fixed constant and fixed power work uniformly over the entire parameter box. -/
theorem powerPolynomial_eval_box_bound (k J : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (params : List (ℤ × ℤ)) (hlen : params.length ≤ J)
    (hm : ∀ p ∈ params, p.2 ≠ 0)
    (hbox : ∀ p ∈ params, |(p.1 : ℝ)| ≤ P ∧ |(p.2 : ℝ)| ≤ P)
    (z : ℝ) (hz : |z| ≤ P) :
    |(powerPolynomial k params).eval₂ (Int.castRingHom ℝ) z| ≤
      ((2 : ℝ)^J*((J : ℝ)+1)^k)*P^((k+1)*k) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hpow : P ≤ P^(k+1) := by
    simpa only [pow_succ,one_mul] using
      mul_le_mul_of_nonneg_right (one_le_pow₀ (n := k) hP) hP0
  have hlenR : (params.length : ℝ) ≤ J := by exact_mod_cast hlen
  have hradius : |z|+shiftRadius k params ≤ ((J : ℝ)+1)*P^(k+1) := by
    have hr := shiftRadius_le_box k params hP0 hbox
    have hmul := mul_le_mul_of_nonneg_right hlenR (pow_nonneg hP0 (k+1))
    nlinarith
  have hcount : (2 : ℝ)^params.length ≤ (2 : ℝ)^J :=
    pow_le_pow_right₀ (by norm_num) hlen
  calc
    _ ≤ (2 : ℝ)^params.length*(|z|+shiftRadius k params)^k :=
      powerPolynomial_eval_bound k params hm z
    _ ≤ (2 : ℝ)^J*(((J : ℝ)+1)*P^(k+1))^k :=
      mul_le_mul hcount
        (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (shiftRadius_nonneg k params)) hradius k)
        (pow_nonneg (add_nonneg (abs_nonneg _) (shiftRadius_nonneg k params)) _)
        (by positivity)
    _ = _ := by rw [mul_pow,← pow_mul]; ring

/-- At a fixed sufficiently large ambient scale the phase magnitude is
bounded by a pure power, exactly as required by the bad-factor theorem. -/
theorem powerPolynomial_magnitude_polynomial_bound (k J : ℕ) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ params : List (ℤ × ℤ), params.length ≤ J →
      (∀ p ∈ params, p.2 ≠ 0) →
      (∀ p ∈ params, |(p.1 : ℝ)| ≤ P ∧ |(p.2 : ℝ)| ≤ P) →
      ∀ z : ℤ, |(z : ℝ)| ≤ P →
      (((powerPolynomial k params).eval z).natAbs : ℝ) ≤
        P^(((k+1)*k+1 : ℕ) : ℝ) := by
  let C : ℝ := (2 : ℝ)^J*((J : ℝ)+1)^k
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro P hPP₀ params hlen hm hbox z hz
  have hP : 1 ≤ P := (le_max_left _ _).trans hPP₀
  have hCP : C ≤ P := (le_max_right _ _).trans hPP₀
  have heval := Polynomial.eval₂_at_apply (p := (powerPolynomial k params))
    (Int.castRingHom ℝ) z
  change (powerPolynomial k params).eval₂ (Int.castRingHom ℝ) (z : ℝ) =
    (((powerPolynomial k params).eval z : ℤ) : ℝ) at heval
  have habs : (((powerPolynomial k params).eval z).natAbs : ℝ) =
      |(powerPolynomial k params).eval₂ (Int.castRingHom ℝ) (z : ℝ)| := by
    rw [heval,Nat.cast_natAbs,Int.cast_abs]
  rw [habs,Real.rpow_natCast]
  calc
    _ ≤ C*P^((k+1)*k) := powerPolynomial_eval_box_bound k J hP params hlen hm hbox (z : ℝ) hz
    _ ≤ P*P^((k+1)*k) :=
      mul_le_mul_of_nonneg_right hCP (pow_nonneg (zero_le_one.trans hP) _)
    _ = P^((k+1)*k+1) := by rw [pow_succ]; ring

#print axioms powerPolynomial_eval_bound
#print axioms powerPolynomial_magnitude_polynomial_bound
end Waring.IntegerDifferencePolynomial
