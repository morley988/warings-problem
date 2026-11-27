import Waring.SeedCompletionEvenTriple

/-! # Exact integer normalization of the even third phase -/

noncomputable section
namespace Waring.SeedCompletionEvenTriple
open IntegerDifferencePolynomial Polynomial FirstDifferenceSecond
open SeedCompletionEvenDouble (Pair)

/-- Polynomial equality gives the actual old phase at both shifted centers,
including negative ones. -/
theorem doublePolynomial_eq_powerPolynomial {d : ℕ} (hd : supportedHalfDegree d)
    (h m : Pair) (hm₁ : 0 < m.1) (hm₂ : 0 < m.2) :
    SeedCompletionEvenDouble.phasePolynomial d h m =
      powerPolynomial (2*d) [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))] := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
  rintro z ⟨n,rfl⟩
  exact (SeedCompletionEvenDouble.phasePolynomial_eval d h m n).trans
    (SeedCompletionEvenDouble.phase_eq_powerPolynomial hd h m n hm₁ hm₂)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
theorem phase_eq_old_difference {d : ℕ} (hd : supportedHalfDegree d)
    (h : Heights) (m : Pair) (z : ℕ) :
    (phase d h m z : ℤ)=
      (SeedCompletionEvenDouble.phasePolynomial d h.1 m).eval ((z : ℤ)+(h.2 : ℤ))-
      (SeedCompletionEvenDouble.phasePolynomial d h.1 m).eval ((z : ℤ)-(h.2 : ℤ)) := by
  rcases hd with rfl | rfl | rfl <;>
    norm_num [phase,coefficient,exponent,SeedCompletionEvenDouble.phasePolynomial,
      SeedCompletionEvenDouble.coefficient,SeedCompletionEvenDouble.exponent,
      Polynomial.eval_finset_sum,Polynomial.eval_monomial,Finset.sum_range_succ,Nat.choose] <;> ring

theorem phase_eq_powerPolynomial {d : ℕ} (hd : supportedHalfDegree d)
    (h : Heights) (m : Pair) (z : ℕ) (hm₁ : 0 < m.1) (hm₂ : 0 < m.2) :
    (phase d h m z : ℤ)=
      (powerPolynomial (2*d) [((h.2 : ℤ),1),((h.1.2 : ℤ),(m.2 : ℤ)),
        ((h.1.1 : ℤ),(m.1 : ℤ))]).eval (z : ℤ) := by
  rw [phase_eq_old_difference hd,doublePolynomial_eq_powerPolynomial hd h.1 m hm₁ hm₂]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul (2*d) (h.2 : ℤ) 1
      (powerPolynomial (2*d) [((h.1.2 : ℤ),(m.2 : ℤ)),((h.1.1 : ℤ),(m.1 : ℤ))]))
  symm
  simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,one_pow,mul_one,one_mul] using H

#print axioms doublePolynomial_eq_powerPolynomial
#print axioms phase_eq_powerPolynomial
end Waring.SeedCompletionEvenTriple
