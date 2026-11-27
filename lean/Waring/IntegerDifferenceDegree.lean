import Waring.IntegerDifferencePolynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Exact degree and nonsingularity of the source difference polynomials

For nonzero integer heights and coefficients, each normalized centered
difference lowers a positive degree by exactly one. Its new leading
coefficient is 2*h*n times the old leading coefficient. Consequently the
derivative is a nonzero polynomial throughout all source stages j<k.
-/

noncomputable section
namespace Waring.IntegerDifferencePolynomial
open Polynomial

theorem taylor_coeff_pred (p : Polynomial ℤ) (a : ℤ) (hn : 0 < p.natDegree) :
    (taylor a p).coeff (p.natDegree-1) =
      (p.natDegree : ℤ)*p.leadingCoeff*a + p.coeff (p.natDegree-1) := by
  have hdeg : (hasseDeriv (p.natDegree-1) p).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le _ _).trans (by omega)
  have hlinear := eq_X_add_C_of_natDegree_le_one hdeg
  rw [taylor_coeff,hlinear]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.hasseDeriv_coeff,zero_add,Nat.choose_self,Nat.cast_one,one_mul]
  have hnid : 1+(p.natDegree-1) = p.natDegree := by omega
  rw [hnid,show p.natDegree.choose (p.natDegree-1)=p.natDegree by
    have h := Nat.choose_succ_self_right (p.natDegree-1)
    simpa only [Nat.sub_add_cancel hn] using h,coeff_natDegree]

/-- The coefficient immediately below the old degree is retained exactly. -/
theorem difference_coeff_pred (k : ℕ) (h m : ℤ) (p : Polynomial ℤ)
    (hm : m ≠ 0) (hn : 0 < p.natDegree) :
    (difference k h m p).coeff (p.natDegree-1) =
      2*h*(p.natDegree : ℤ)*p.leadingCoeff := by
  have H := congrArg (fun q : Polynomial ℤ => q.coeff (p.natDegree-1))
    (difference_mul k h m p)
  change (C (m^k)*difference k h m p).coeff (p.natDegree-1) =
    (p.comp (X+C (h*m^k))-p.comp (X-C (h*m^k))).coeff (p.natDegree-1) at H
  have heq : X-C (h*m^k) = X+C (-(h*m^k)) := by simp [sub_eq_add_neg]
  rw [Polynomial.coeff_C_mul,heq] at H
  change m^k*(difference k h m p).coeff (p.natDegree-1) =
    (taylor (h*m^k) p-taylor (-(h*m^k)) p).coeff (p.natDegree-1) at H
  rw [Polynomial.coeff_sub,taylor_coeff_pred p _ hn,taylor_coeff_pred p _ hn] at H
  apply mul_left_cancel₀ (pow_ne_zero k hm)
  linear_combination H

theorem difference_natDegree (k : ℕ) (h m : ℤ) (p : Polynomial ℤ)
    (hh : h ≠ 0) (hm : m ≠ 0) (hn : 0 < p.natDegree) :
    (difference k h m p).natDegree = p.natDegree-1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (difference_natDegree_le k h m p hm)
  rw [difference_coeff_pred k h m p hm hn]
  have hnZ : (p.natDegree : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : p ≠ 0 := by intro hz; simp [hz] at hn
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) hnZ)
    (Polynomial.leadingCoeff_ne_zero.mpr hp)

/-- No accidental degree loss occurs in the actual source recursion. -/
theorem powerPolynomial_natDegree (k : ℕ) (params : List (ℤ × ℤ))
    (hhm : ∀ p ∈ params, p.1 ≠ 0 ∧ p.2 ≠ 0) (hlen : params.length ≤ k) :
    (powerPolynomial k params).natDegree = k-params.length := by
  induction params with
  | nil => simp [powerPolynomial]
  | cons p rest ih =>
    simp only [List.length_cons] at hlen
    have hrest : ∀ q ∈ rest, q.1 ≠ 0 ∧ q.2 ≠ 0 :=
      fun q hq => hhm q (List.mem_cons_of_mem _ hq)
    have hlenrest : rest.length ≤ k := by omega
    have hprev := ih hrest hlenrest
    have hn : 0 < (powerPolynomial k rest).natDegree := by
      rw [hprev]
      omega
    rw [powerPolynomial,difference_natDegree k p.1 p.2 _
      (hhm p (List.mem_cons_self ..)).1 (hhm p (List.mem_cons_self ..)).2 hn,hprev]
    simp only [List.length_cons,Nat.sub_sub]

/-- The derivative-zero term is genuinely a finite root problem at every
stage before the kth difference. -/
theorem powerPolynomial_derivative_ne_zero (k : ℕ) (params : List (ℤ × ℤ))
    (hhm : ∀ p ∈ params, p.1 ≠ 0 ∧ p.2 ≠ 0) (hlen : params.length < k) :
    (powerPolynomial k params).derivative ≠ 0 := by
  intro hz
  have hzero := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hz
  have hdeg := powerPolynomial_natDegree k params hhm hlen.le
  omega

#print axioms difference_coeff_pred
#print axioms powerPolynomial_natDegree
#print axioms powerPolynomial_derivative_ne_zero
end Waring.IntegerDifferencePolynomial
