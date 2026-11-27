import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-! # Integral polynomial phase descent

The normalized difference has integral coefficients. On any residue
ring in which the step vanishes, it specializes to the formal derivative.
The construction uses no division in the coefficient ring.
-/

namespace WaringLinear
open Polynomial
open scoped BigOperators

section
variable {R S : Type*} [CommRing R] [CommRing S]

def powerDifference (x h : R) : ℕ → R
  | 0 => 0
  | n+1 => (x+h)^n+x*powerDifference x h n

theorem mul_powerDifference (x h : R) (n : ℕ) :
    h*powerDifference x h n=(x+h)^n-x^n := by
  induction n with
  | zero => simp [powerDifference]
  | succ n ih =>
    simp only [powerDifference,pow_succ]
    linear_combination x*ih

theorem map_powerDifference (ρ : R →+* S) (x h : R) (n : ℕ) :
    ρ (powerDifference x h n)=powerDifference (ρ x) (ρ h) n := by
  induction n with
  | zero => simp [powerDifference]
  | succ n ih => simp [powerDifference,ih]

theorem powerDifference_zero (x : R) (n : ℕ) :
    powerDifference x 0 n = (n:R)*x^(n-1) := by
  cases n with
  | zero => simp [powerDifference]
  | succ n =>
    induction n with
    | zero => simp [powerDifference]
    | succ n ih =>
      simp only [powerDifference,add_zero,Nat.succ_sub_one,Nat.cast_succ] at ih ⊢
      rw [show x^n+x*powerDifference x 0 n=((n:R)+1)*x^n from ih]
      rw [pow_succ]; ring

/-- Evaluate the integral normalized difference polynomial at x. -/
def polynomialDifference (P : R[X]) (x h : R) : R :=
  P.sum (fun n a => a*powerDifference x h n)

theorem mul_polynomialDifference (P : R[X]) (x h : R) :
    h*polynomialDifference P x h = P.eval (x+h)-P.eval x := by
  simp only [polynomialDifference,Polynomial.eval_eq_sum,Polynomial.sum,Finset.mul_sum,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = P.coeff n*(h*powerDifference x h n) := by ring
    _ = _ := by rw [mul_powerDifference]; ring

/-- In every quotient where the step h is zero, the normalized difference
specializes to the formal derivative. This applies to the polynomial-ring
coefficient case as well, hence coefficientwise to the actual phase. -/
theorem map_polynomialDifference_eq_derivative (ρ : R →+* S) (P : R[X]) (x h : R)
    (hh : ρ h=0) :
    ρ (polynomialDifference P x h) = ρ (P.derivative.eval x) := by
  simp only [polynomialDifference,Polynomial.derivative_eval,Polynomial.sum,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul,map_powerDifference,hh,powerDifference_zero]
  simp [mul_assoc]

end
#print axioms mul_polynomialDifference
#print axioms map_polynomialDifference_eq_derivative
end WaringLinear
