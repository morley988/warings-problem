import Waring.EndgameCompletionDiscrete
import Mathlib.Algebra.Polynomial.Derivative

/-!
# First-derivative cancellation for positive-coefficient polynomial phases

The source centered-difference phases have nonnegative coefficients at
positive parameters. Their finite increments are nonnegative and monotone.
The actual summation-by-parts estimate therefore applies uniformly to
every nonzero completion frequency, with the derivative evaluated only at
the upper endpoint.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.PolicyCompletionPolynomialDiscrete
open Polynomial QuadraticModulation EndgameCompletion

def NonnegativeCoefficients (f : Polynomial ℝ) : Prop := ∀ i, 0 ≤ f.coeff i

theorem eval_nonneg (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (pow_nonneg hx i))

theorem derivative_nonnegative (f : Polynomial ℝ) (hf : NonnegativeCoefficients f) :
    NonnegativeCoefficients f.derivative := by
  intro i
  rw [Polynomial.coeff_derivative]
  exact mul_nonneg (hf (i+1)) (by positivity)

theorem eval_monotone (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : f.eval x ≤ f.eval y := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy i) (hf i))

def polynomialIncrement (f : Polynomial ℝ) (n : ℕ) : ℝ :=
  f.eval ((n:ℝ)+1)-f.eval (n:ℝ)

theorem polynomialIncrement_eq (f : Polynomial ℝ) (n : ℕ) :
    polynomialIncrement f n =
      ∑ i ∈ f.support, f.coeff i * monomialIncrement i n := by
  simp only [polynomialIncrement, Polynomial.eval_eq_sum, Polynomial.sum,
    ← Finset.sum_sub_distrib, monomialIncrement, Nat.cast_add, Nat.cast_one, mul_sub]

theorem polynomialIncrement_nonneg (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) (n : ℕ) : 0 ≤ polynomialIncrement f n := by
  rw [polynomialIncrement_eq]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (monomialIncrement_nonneg i n))

theorem polynomialIncrement_monotone (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) : Monotone (polynomialIncrement f) := by
  intro n m hnm
  simp only [polynomialIncrement_eq]
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (monomialIncrement_monotone i hnm) (hf i))

theorem polynomialIncrement_le (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) (n : ℕ) :
    polynomialIncrement f n ≤ f.derivative.eval ((n:ℝ)+1) := by
  rw [polynomialIncrement_eq, Polynomial.derivative_eval, Polynomial.sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc, Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_left (monomialIncrement_le i n) (hf i)

theorem polynomial_increment_variation (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) (N : ℕ) (β θ : ℝ) :
    (∑ n ∈ Finset.range N,
      |(β*polynomialIncrement f (n+1)-θ)-(β*polynomialIncrement f n-θ)|) ≤
        |β| *f.derivative.eval ((N:ℝ)+1) := by
  have heq (n : ℕ) :
      |(β*polynomialIncrement f (n+1)-θ)-(β*polynomialIncrement f n-θ)| =
        |β| *(polynomialIncrement f (n+1)-polynomialIncrement f n) := by
    rw [show (β*polynomialIncrement f (n+1)-θ)-(β*polynomialIncrement f n-θ)=
      β*(polynomialIncrement f (n+1)-polynomialIncrement f n) by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr (polynomialIncrement_monotone f hf (Nat.le_succ n)))]
  simp_rw [heq]
  rw [← Finset.mul_sum, Finset.sum_range_sub]
  exact mul_le_mul_of_nonneg_left
    ((sub_le_self _ (polynomialIncrement_nonneg f hf 0)).trans
      (polynomialIncrement_le f hf N)) (abs_nonneg _)

theorem norm_polynomial_linear_sum_le (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) (N : ℕ) (hN : 1 ≤ N) (β θ : ℝ)
    (hθ : 0 < integerDistance θ)
    (hsmall : |β| *f.derivative.eval (N:ℝ) ≤ integerDistance θ/2) :
    ‖∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)-θ*n)‖ ≤
      (1+Real.pi/4)/integerDistance θ := by
  let z : ℕ → ℂ := fun n => e (β*f.eval (n:ℝ)-θ*n)
  let δ : ℕ → ℝ := fun n => β*polynomialIncrement f n-θ
  let V : ℝ := |β| *f.derivative.eval (N:ℝ)
  have hstep (n : ℕ) : z (n+1)=z n*e (δ n) := by
    dsimp [z, δ, polynomialIncrement]
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hperturb (n : ℕ) (hn : n ≤ N-1) : |δ n-(-θ)| ≤ V := by
    dsimp [δ, V]
    rw [sub_neg_eq_add, sub_add_cancel, abs_mul,
      abs_of_nonneg (polynomialIncrement_nonneg f hf n)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (polynomialIncrement_le f hf n).trans
      (eval_monotone f.derivative (derivative_nonnegative f hf) (by positivity)
        (by exact_mod_cast (show n+1 ≤ N by omega)))
  have hchord (n : ℕ) (hn : n ≤ N-1) :
      2*integerDistance θ ≤ ‖e (δ n)-1‖ := by
    have hdist := integerDistance_le_add_abs_sub (-θ) (δ n)
    rw [integerDistance_neg_eq, abs_sub_comm] at hdist
    have hlower := chord_distance_lower (δ n)
    rw [← e_eq_unitCharacter] at hlower
    have hpert := hperturb n hn
    change V ≤ integerDistance θ/2 at hsmall
    linarith
  have hvar : (∑ n ∈ Finset.range (N-1), |δ (n+1)-δ n|) ≤ V := by
    have heq : ((N-1:ℕ):ℝ)+1 = (N:ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    simpa only [δ, V, heq] using polynomial_increment_variation f hf (N-1) β θ
  have h := norm_sum_varying_phase_le z δ (N-1) (D := 2*integerDistance θ)
    (V := V) (by positivity) (fun n _ => (norm_e _).le)
    (fun n _ => hstep n) hchord hvar
  simp only [Nat.sub_add_cancel hN] at h
  apply h.trans
  have hbound : 2/(2*integerDistance θ)+(2*Real.pi/(2*integerDistance θ)^2)*V ≤
      2/(2*integerDistance θ)+(2*Real.pi/(2*integerDistance θ)^2)*(integerDistance θ/2) := by
    gcongr
  apply hbound.trans_eq
  field_simp
  ring

theorem norm_polynomial_positive_sum_le (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) (N : ℕ) (β θ : ℝ)
    (hθ : 0 < integerDistance θ)
    (hsmall : |β| *f.derivative.eval (N:ℝ) ≤ integerDistance θ/2) :
    ‖∑ n ∈ Finset.Icc 1 N, e (β*f.eval (n:ℝ)-θ*n)‖ ≤
      2+(1+Real.pi/4)/integerDistance θ := by
  by_cases hN : N=0
  · subst N
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0<1), Finset.sum_empty, norm_zero]
    positivity
  have hsum := norm_polynomial_linear_sum_le f hf N (by omega) β θ hθ hsmall
  have hid : (∑ n ∈ Finset.Icc 1 N, e (β*f.eval (n:ℝ)-θ*n)) =
      (∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)-θ*n))+
        e (β*f.eval (N:ℝ)-θ*N)-e (β*f.eval 0-θ*0) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
      Finset.sum_Ico_eq_sub _ (by omega : 1≤N+1),
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero]
  rw [hid]
  calc
    _ ≤ ‖(∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)-θ*n))+e (β*f.eval (N:ℝ)-θ*N)‖+
        ‖e (β*f.eval 0-θ*0)‖ := norm_sub_le _ _
    _ ≤ (‖∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)-θ*n)‖+‖e (β*f.eval (N:ℝ)-θ*N)‖)+
        ‖e (β*f.eval 0-θ*0)‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ _ := by simp only [norm_e]; linarith

#print axioms norm_polynomial_linear_sum_le
#print axioms norm_polynomial_positive_sum_le
end Waring.PolicyCompletionPolynomialDiscrete
