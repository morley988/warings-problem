import Waring.SeedCompletionNinthTriple

/-! # Exact normalization and polynomial identity for the degree-nine third phase -/

noncomputable section
namespace Waring.SeedCompletionNinthTriple
open IntegerDifferencePolynomial Polynomial
open SeedCompletionNinthDouble (Pair)

/-- The full old center polynomial is the actual integer second difference,
so it may be evaluated at either sign of the next shifted center. -/
theorem doublePolynomial_eq_powerPolynomial (h m : Pair)
    (hm₁ : 0 < m.1) (hm₂ : 0 < m.2) :
    SeedCompletionNinthDouble.doublePolynomial h m =
      powerPolynomial 9 [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))] := by
  have hm1 : (m.1 : ℤ)^9 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₁.ne')
  have hm2 : (m.2 : ℤ)^9 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₂.ne')
  apply Polynomial.funext
  intro z
  apply mul_left_cancel₀ (mul_ne_zero hm1 hm2)
  have H := congrArg (fun p : Polynomial ℤ => p.eval z)
    (difference_mul 9 (h.2 : ℤ) (m.2 : ℤ)
      (powerPolynomial 9 [((h.1 : ℤ),(m.1 : ℤ))]))
  have H' : (m.2 : ℤ)^9*
      (powerPolynomial 9 [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))]).eval z =
      (powerPolynomial 9 [((h.1 : ℤ),(m.1 : ℤ))]).eval
        (z+(h.2 : ℤ)*(m.2 : ℤ)^9) -
      (powerPolynomial 9 [((h.1 : ℤ),(m.1 : ℤ))]).eval
        (z-(h.2 : ℤ)*(m.2 : ℤ)^9) := by
    simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X] using H
  conv_rhs =>
    rw [mul_assoc,H',mul_sub,SeedCompletionEvenSecond.first_mul_identity,
      SeedCompletionEvenSecond.first_mul_identity]
  simp only [SeedCompletionNinthDouble.doublePolynomial,Polynomial.eval_add,
    Polynomial.eval_monomial,SeedCompletionNinthDouble.leadingFactor,
    SeedCompletionNinthDouble.amplitude]
  push_cast
  ring

theorem phase_eq_old_difference (h : Heights) (m : Pair) (z : ℕ) :
    (phase h m z : ℤ)=
      (SeedCompletionNinthDouble.doublePolynomial h.1 m).eval ((z : ℤ)+(h.2 : ℤ))-
      (SeedCompletionNinthDouble.doublePolynomial h.1 m).eval ((z : ℤ)-(h.2 : ℤ)) := by
  simp only [phase,leadingFactor,middle,low,constant,
    SeedCompletionNinthDouble.doublePolynomial,Polynomial.eval_add,
    Polynomial.eval_monomial,SeedCompletionNinthDouble.leadingFactor]
  push_cast
  ring

theorem phase_eq_powerPolynomial (h : Heights) (m : Pair) (z : ℕ)
    (hm₁ : 0 < m.1) (hm₂ : 0 < m.2) :
    (phase h m z : ℤ)=
      (powerPolynomial 9 [((h.2 : ℤ),1),((h.1.2 : ℤ),(m.2 : ℤ)),
        ((h.1.1 : ℤ),(m.1 : ℤ))]).eval (z : ℤ) := by
  rw [phase_eq_old_difference,doublePolynomial_eq_powerPolynomial h.1 m hm₁ hm₂]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul 9 (h.2 : ℤ) 1
      (powerPolynomial 9 [((h.1.2 : ℤ),(m.2 : ℤ)),((h.1.1 : ℤ),(m.1 : ℤ))]))
  symm
  simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,one_pow,mul_one,one_mul] using H

#print axioms doublePolynomial_eq_powerPolynomial
#print axioms phase_eq_powerPolynomial
end Waring.SeedCompletionNinthTriple
