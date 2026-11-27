import Waring.PolicyCompletionEvenLowDegreeBounds
import Waring.SeedCompletionTerminalPhase
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Literal quadratic and quartic polynomial forms of the terminal phases -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionEvenLowDegreePolynomial
open Polynomial PolicyCompletionEvenLowDegreePairs PolicyCompletionEvenLowDegreeBounds

theorem even_low_coefficients (f : Polynomial ℤ) (hd : f.natDegree≤4)
    (hn : ∀i,0≤f.coeff i) (he : f.eval (-1)=f.eval 1) :
    f.coeff 1=0 ∧ f.coeff 3=0 := by
  rw [eval_eq_sum_range' (show f.natDegree<5 by omega),
    eval_eq_sum_range' (show f.natDegree<5 by omega)] at he
  norm_num [Finset.sum_range_succ] at he
  have h1:=hn 1
  have h3:=hn 3
  constructor <;> omega

theorem quadratic_eval (f : Polynomial ℤ) (hd : f.natDegree≤2)
    (h1 : f.coeff 1=0) (z : ℤ) :
    f.eval z=quadraticValue (f.coeff 2) (f.coeff 0) z := by
  rw [eval_eq_sum_range' (show f.natDegree<3 by omega)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one,
    h1,zero_mul,add_zero]
  unfold quadraticValue
  ring

theorem quartic_eval (f : Polynomial ℤ) (hd : f.natDegree≤4)
    (h1 : f.coeff 1=0) (h3 : f.coeff 3=0) (z : ℤ) :
    f.eval z=quarticValue (f.coeff 4) (f.coeff 2) (f.coeff 0) z := by
  rw [eval_eq_sum_range' (show f.natDegree<5 by omega)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one,
    h1,h3,zero_mul,add_zero]
  unfold quarticValue
  ring

theorem quadratic_ext (f g : Polynomial ℤ) (hf : f.natDegree≤2) (hg : g.natDegree≤2)
    (hf1 : f.coeff 1=0) (hg1 : g.coeff 1=0)
    (ha : f.coeff 2=g.coeff 2) (hc : f.coeff 0=g.coeff 0) : f=g := by
  apply Polynomial.ext
  intro i
  by_cases hi : i≤2
  · interval_cases i <;> simp only [hf1,hg1,ha,hc]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i),
      coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < i)]

theorem quartic_ext (f g : Polynomial ℤ) (hf : f.natDegree≤4) (hg : g.natDegree≤4)
    (hf1 : f.coeff 1=0) (hg1 : g.coeff 1=0) (hf3 : f.coeff 3=0) (hg3 : g.coeff 3=0)
    (ha : f.coeff 4=g.coeff 4) (hb : f.coeff 2=g.coeff 2) (hc : f.coeff 0=g.coeff 0) : f=g := by
  apply Polynomial.ext
  intro i
  by_cases hi : i≤4
  · interval_cases i <;> simp only [hf1,hg1,hf3,hg3,ha,hb,hc]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i),
      coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < i)]

theorem nonnegative_coefficient_le_eval_one (f : Polynomial ℤ) (hn : ∀i,0≤f.coeff i) (i : ℕ) :
    f.coeff i≤f.eval 1 := by
  rw [eval_eq_sum,Polynomial.sum]
  simp only [one_pow,mul_one]
  by_cases hi : i∈f.support
  · exact Finset.single_le_sum (fun j _=>hn j) hi
  · rw [notMem_support_iff.mp hi]
    exact Finset.sum_nonneg (fun j _=>hn j)

#print axioms quartic_eval
#print axioms even_low_coefficients
end Waring.PolicyCompletionEvenLowDegreePolynomial
