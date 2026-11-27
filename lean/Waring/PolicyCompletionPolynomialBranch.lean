import Waring.PolicyCompletionPolynomialStationary
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Exact coefficient control under a prime-adic branch substitution

For f'=p^t D and f(r+pX)-f(r)=p^sigma g with g'=p^tau Dnew,
coefficients give sigma+tau<=t+1+nu whenever the nu-th Taylor coefficient
of D is a unit. They also force every higher coefficient of Dnew to be
divisible by p. These are the degree-drop relations behind Hua recursion.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialBranch
open Polynomial

def shiftedDifference (f : Polynomial ℤ) (p r : ℤ) : Polynomial ℤ :=
  f.comp (C p*X+C r)-C (f.eval r)

theorem shiftedDifference_derivative (f : Polynomial ℤ) (p r : ℤ) :
    (shiftedDifference f p r).derivative=C p*f.derivative.comp (C p*X+C r) := by
  simp [shiftedDifference,derivative_comp]

theorem affine_comp_coeff (f : Polynomial ℤ) (p r : ℤ) (j : ℕ) :
    (f.comp (C p*X+C r)).coeff j=(taylor r f).coeff j*p^j := by
  have he : f.comp (C p*X+C r)=(taylor r f).comp (C p*X) := by
    simp [taylor_apply,comp_assoc]
  rw [he,comp_C_mul_X_coeff]

/-- The integer coefficient identity retains both derivative contents. -/
theorem branch_derivative_coeff (f D g Dnew : Polynomial ℤ) (p r : ℤ)
    (t σ τ j : ℕ) (hder : f.derivative=C (p^t)*D)
    (hbranch : shiftedDifference f p r=C (p^σ)*g)
    (hnew : g.derivative=C (p^τ)*Dnew) :
    p^(σ+τ)*Dnew.coeff j=p^(t+1+j)*(taylor r D).coeff j := by
  have he := congrArg Polynomial.derivative hbranch
  rw [shiftedDifference_derivative,derivative_C_mul,hder,hnew,C_mul_comp] at he
  have hc := congrArg (fun F : Polynomial ℤ => F.coeff j) he
  simp only [coeff_C_mul,affine_comp_coeff] at hc
  calc
    _ = p^σ*(p^τ*Dnew.coeff j) := by rw [pow_add]; ring
    _ = p*(p^t*((taylor r D).coeff j*p^j)) := hc.symm
    _ = _ := by rw [pow_add,pow_add,pow_one]; ring

theorem power_order_le_of_not_dvd {p a : ℤ} (hp : p ≠ 0)
    {m n : ℕ} (ha : ¬p ∣ a) (hdiv : p^m ∣ p^n*a) : m ≤ n := by
  by_contra hmn
  have hn : n+1 ≤ m := by omega
  have hd : p^(n+1) ∣ p^n*a := (pow_dvd_pow p hn).trans hdiv
  rw [pow_succ] at hd
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero n hp)).mp hd)

/-- A nonzero Taylor coefficient bounds the total branch content. -/
theorem branch_content_le (f D g Dnew : Polynomial ℤ) {p r : ℤ} (hp : p ≠ 0)
    (t σ τ ν : ℕ) (hder : f.derivative=C (p^t)*D)
    (hbranch : shiftedDifference f p r=C (p^σ)*g)
    (hnew : g.derivative=C (p^τ)*Dnew)
    (hν : ¬p ∣ (taylor r D).coeff ν) : σ+τ ≤ t+1+ν := by
  apply power_order_le_of_not_dvd hp hν
  rw [← branch_derivative_coeff f D g Dnew p r t σ τ ν hder hbranch hnew]
  exact dvd_mul_right _ _

/-- Every coefficient beyond that Taylor index vanishes modulo p. -/
theorem branch_high_coeff_dvd (f D g Dnew : Polynomial ℤ) {p r : ℤ} (hp : p ≠ 0)
    (t σ τ ν : ℕ) (hder : f.derivative=C (p^t)*D)
    (hbranch : shiftedDifference f p r=C (p^σ)*g)
    (hnew : g.derivative=C (p^τ)*Dnew)
    (hν : ¬p ∣ (taylor r D).coeff ν) (j : ℕ) (hj : ν < j) :
    p ∣ Dnew.coeff j := by
  have hle := branch_content_le f D g Dnew hp t σ τ ν hder hbranch hnew hν
  have hd : p^(σ+τ+1) ∣ p^(σ+τ)*Dnew.coeff j := by
    rw [branch_derivative_coeff f D g Dnew p r t σ τ j hder hbranch hnew]
    exact (pow_dvd_pow p (by omega : σ+τ+1 ≤ t+1+j)).trans (dvd_mul_right _ _)
  rw [pow_succ] at hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero (σ+τ) hp)).mp hd

/-- The new primitive derivative has degree at most the old root's
multiplicity once that index is identified by Taylor coefficients. -/
theorem branch_reduced_derivative_degree_le (f D g Dnew : Polynomial ℤ)
    {p : ℕ} (hp : 0 < p) (r : ℤ) (t σ τ ν : ℕ)
    (hder : f.derivative=C ((p : ℤ)^t)*D)
    (hbranch : shiftedDifference f (p : ℤ) r=C ((p : ℤ)^σ)*g)
    (hnew : g.derivative=C ((p : ℤ)^τ)*Dnew)
    (hν : ¬(p : ℤ) ∣ (taylor r D).coeff ν) :
    (Dnew.map (Int.castRingHom (ZMod p))).natDegree ≤ ν := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [Polynomial.coeff_map]
  change ((Dnew.coeff j : ℤ) : ZMod p)=0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact branch_high_coeff_dvd f D g Dnew (by exact_mod_cast hp.ne')
    t σ τ ν hder hbranch hnew hν j hj

#print axioms branch_derivative_coeff
#print axioms branch_content_le
#print axioms branch_reduced_derivative_degree_le
end Waring.PolicyCompletionPolynomialBranch
