import Waring.SeedCompletionEvenDouble

/-! # Exact integer normalization of the even second phase -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenDouble
open IntegerDifferencePolynomial FirstDifferenceSecond

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2400000 in
theorem phase_mul_identity {d : ℕ} (hd : supportedHalfDegree d) (h m : Pair) (z : ℕ) :
    (m.1 : ℤ)^(2*d)*(m.2 : ℤ)^(2*d)*(phase d h m z : ℤ) =
      ((((z : ℤ)+(h.2 : ℤ)*(m.2 : ℤ)^(2*d))+(h.1 : ℤ)*(m.1 : ℤ)^(2*d))^(2*d) -
        (((z : ℤ)+(h.2 : ℤ)*(m.2 : ℤ)^(2*d))-(h.1 : ℤ)*(m.1 : ℤ)^(2*d))^(2*d)) -
      ((((z : ℤ)-(h.2 : ℤ)*(m.2 : ℤ)^(2*d))+(h.1 : ℤ)*(m.1 : ℤ)^(2*d))^(2*d) -
        (((z : ℤ)-(h.2 : ℤ)*(m.2 : ℤ)^(2*d))-(h.1 : ℤ)*(m.1 : ℤ)^(2*d))^(2*d)) := by
  rcases hd with rfl | rfl | rfl <;>
    norm_num [phase,coefficient,exponent,Finset.sum_range_succ,Nat.choose] <;> ring

/-- Both coefficient powers are canceled through actual integer
multiplication identities; no rational-frequency proxy is introduced. -/
theorem phase_eq_powerPolynomial {d : ℕ} (hd : supportedHalfDegree d)
    (h m : Pair) (z : ℕ) (hm₁ : 0 < m.1) (hm₂ : 0 < m.2) :
    (phase d h m z : ℤ)=
      (powerPolynomial (2*d) [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))]).eval (z : ℤ) := by
  have hm1 : (m.1 : ℤ)^(2*d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₁.ne')
  have hm2 : (m.2 : ℤ)^(2*d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₂.ne')
  apply mul_left_cancel₀ (mul_ne_zero hm1 hm2)
  rw [phase_mul_identity hd]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul (2*d) (h.2 : ℤ) (m.2 : ℤ)
      (powerPolynomial (2*d) [((h.1 : ℤ),(m.1 : ℤ))]))
  have H' : (m.2 : ℤ)^(2*d)*
      (powerPolynomial (2*d) [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))]).eval (z : ℤ) =
      (powerPolynomial (2*d) [((h.1 : ℤ),(m.1 : ℤ))]).eval
        ((z : ℤ)+(h.2 : ℤ)*(m.2 : ℤ)^(2*d)) -
      (powerPolynomial (2*d) [((h.1 : ℤ),(m.1 : ℤ))]).eval
        ((z : ℤ)-(h.2 : ℤ)*(m.2 : ℤ)^(2*d)) := by
    simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X] using H
  rw [mul_assoc,H',mul_sub,
    SeedCompletionEvenSecond.first_mul_identity,
    SeedCompletionEvenSecond.first_mul_identity]

#print axioms phase_mul_identity
#print axioms phase_eq_powerPolynomial
end Waring.SeedCompletionEvenDouble
