import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.Ring

/-! # Second-order Taylor expansion over a finite-precision ring -/
namespace WaringLinear
open Polynomial
variable {A : Type*} [CommRing A]

theorem evaluate_cubic_nilpotent_step (f : A[X]) (x t : A) (ht : t^3=0) :
    f.eval (x+t)=f.eval x+f.derivative.eval x*t+(hasseDeriv 2 f).eval x*t^2 := by
  rw [add_comm x t,← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range' ((Nat.lt_succ_self _).trans ((Nat.lt_succ_self _).trans (Nat.lt_succ_self _))),
    Finset.sum_range_succ',Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [pow_zero,mul_one,taylor_coeff_zero,pow_one,taylor_coeff_one,taylor_coeff]
  have h (i : ℕ) : t^(i+1+1+1)=0 := by
    rw [show i+1+1+1=i+3 by omega,pow_add,ht,mul_zero]
  simp [h,add_comm,add_left_comm,add_assoc]

theorem double_hasse_two (f : A[X]) (x : A) :
    2*(hasseDeriv 2 f).eval x=f.derivative.derivative.eval x := by
  have h := congrArg (fun g : A[X] => g.eval x)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R:=A) 2) f)
  simpa [Nat.factorial_succ,two_nsmul,two_mul,Function.iterate_succ_apply] using h

#print axioms evaluate_cubic_nilpotent_step
#print axioms double_hasse_two
end WaringLinear
