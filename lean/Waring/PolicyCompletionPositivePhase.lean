import Waring.PolicyCompletionPolynomialDiscrete
import Waring.IntegerDifferenceSize

/-!
# Positivity of the actual centered-difference polynomials

Positive heights and coefficients preserve nonnegative coefficients under
each normalized centered difference. This proves the convexity hypotheses
needed by the major-arc cancellation lemmas for the literal source phase.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPositivePhase
open Polynomial IntegerDifferencePolynomial PolicyCompletionPolynomialDiscrete

theorem eval_neg_le_eval (f : Polynomial ℤ) (hf : ∀ i, 0 ≤ f.coeff i)
    {a : ℤ} (ha : 0 ≤ a) : f.eval (-a) ≤ f.eval a := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hf i)
  exact (le_abs_self ((-a)^i)).trans_eq (by rw [abs_pow, abs_neg, abs_of_nonneg ha])

theorem difference_coeff_nonneg (k : ℕ) {h m : ℤ} (hh : 0 ≤ h) (hm : 0 < m)
    (f : Polynomial ℤ) (hf : ∀ i, 0 ≤ f.coeff i) (i : ℕ) :
    0 ≤ (difference k h m f).coeff i := by
  have hid := congrArg (fun F : Polynomial ℤ => F.coeff i) (difference_mul k h m f)
  change (C (m^k)*difference k h m f).coeff i =
    (f.comp (X+C (h*m^k))-f.comp (X-C (h*m^k))).coeff i at hid
  rw [Polynomial.coeff_C_mul, show X-C (h*m^k) = X+C (-(h*m^k)) by simp [sub_eq_add_neg]] at hid
  change m^k*(difference k h m f).coeff i =
    (taylor (h*m^k) f-taylor (-(h*m^k)) f).coeff i at hid
  rw [Polynomial.coeff_sub, taylor_coeff, taylor_coeff] at hid
  have hhasse : ∀ j, 0 ≤ (hasseDeriv i f).coeff j := by
    intro j
    rw [hasseDeriv_coeff]
    exact mul_nonneg (Nat.cast_nonneg _) (hf _)
  have hrhs := sub_nonneg.mpr (eval_neg_le_eval (hasseDeriv i f) hhasse
    (mul_nonneg hh (pow_nonneg hm.le k)))
  rw [← hid] at hrhs
  exact nonneg_of_mul_nonneg_right hrhs (pow_pos hm k)

theorem powerPolynomial_coeff_nonneg (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0 ≤ hm.1 ∧ 0 < hm.2) (i : ℕ) :
    0 ≤ (powerPolynomial k params).coeff i := by
  induction params generalizing i with
  | nil => simp [powerPolynomial, Polynomial.coeff_X_pow]; split_ifs <;> norm_num
  | cons hm rest ih =>
    exact difference_coeff_nonneg k (hparams hm (List.mem_cons_self ..)).1
      (hparams hm (List.mem_cons_self ..)).2 _
      (fun j => ih (fun p hp => hparams p (List.mem_cons_of_mem _ hp)) j) i

theorem powerPolynomial_real_nonnegative (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0 ≤ hm.1 ∧ 0 < hm.2) :
    NonnegativeCoefficients ((powerPolynomial k params).map (Int.castRingHom ℝ)) := by
  intro i
  rw [Polynomial.coeff_map]
  change 0 ≤ (((powerPolynomial k params).coeff i : ℤ) : ℝ)
  exact_mod_cast powerPolynomial_coeff_nonneg k params hparams i

theorem difference_leadingCoeff (k : ℕ) (h m : ℤ) (f : Polynomial ℤ)
    (hh : h ≠ 0) (hm : m ≠ 0) (hf : 0 < f.natDegree) :
    (difference k h m f).leadingCoeff = 2*h*(f.natDegree : ℤ)*f.leadingCoeff := by
  rw [Polynomial.leadingCoeff, difference_natDegree k h m f hh hm hf,
    difference_coeff_pred k h m f hm hf]

theorem powerPolynomial_leadingCoeff_pos (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0 < hm.1 ∧ 0 < hm.2) (hlen : params.length ≤ k) :
    0 < (powerPolynomial k params).leadingCoeff := by
  induction params with
  | nil => simp [powerPolynomial]
  | cons hm rest ih =>
    have hrest : ∀ p ∈ rest, 0 < p.1 ∧ 0 < p.2 :=
      fun p hp => hparams p (List.mem_cons_of_mem _ hp)
    have hlenrest : rest.length ≤ k := by simpa only [List.length_cons] using Nat.le_of_succ_le hlen
    have hdeg : 0 < (powerPolynomial k rest).natDegree := by
      rw [powerPolynomial_natDegree k rest (fun p hp => ⟨(hrest p hp).1.ne', (hrest p hp).2.ne'⟩) hlenrest]
      simp only [List.length_cons] at hlen
      omega
    rw [powerPolynomial, difference_leadingCoeff k hm.1 hm.2 _
      (hparams hm (List.mem_cons_self ..)).1.ne' (hparams hm (List.mem_cons_self ..)).2.ne' hdeg]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (hparams hm (List.mem_cons_self ..)).1)
      (by exact_mod_cast hdeg)) (ih hrest hlenrest)

theorem derivative_eval_pos (f : Polynomial ℤ) (hf : ∀ i, 0 ≤ f.coeff i)
    (hdeg : 0 < f.natDegree) (hlead : 0 < f.leadingCoeff)
    {z : ℤ} (hz : 0 < z) : 0 < f.derivative.eval z := by
  rw [Polynomial.derivative_eval, Polynomial.sum]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (hf i) (Nat.cast_nonneg _)) (pow_nonneg hz.le _)
  · refine ⟨f.natDegree, Polynomial.mem_support_iff.mpr ?_, ?_⟩
    · simpa only [Polynomial.coeff_natDegree] using hlead.ne'
    · rw [Polynomial.coeff_natDegree]
      exact mul_pos (mul_pos hlead (by exact_mod_cast hdeg)) (pow_pos hz _)

theorem eval_strictMonoOn (f : Polynomial ℤ) (hf : ∀ i, 0 ≤ f.coeff i)
    (hdeg : 0 < f.natDegree) (hlead : 0 < f.leadingCoeff) :
    StrictMonoOn f.eval (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy.le _) (hf i)
  · refine ⟨f.natDegree, Polynomial.mem_support_iff.mpr ?_, ?_⟩
    · simpa only [Polynomial.coeff_natDegree] using hlead.ne'
    · rw [Polynomial.coeff_natDegree]
      exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx hdeg.ne') hlead

theorem powerPolynomial_derivative_eval_pos (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0 < hm.1 ∧ 0 < hm.2) (hlen : params.length < k)
    {z : ℤ} (hz : 0 < z) : 0 < (powerPolynomial k params).derivative.eval z := by
  apply derivative_eval_pos _ (fun i => powerPolynomial_coeff_nonneg k params
    (fun hm hhm => ⟨(hparams hm hhm).1.le, (hparams hm hhm).2⟩) i)
  · rw [powerPolynomial_natDegree k params
      (fun hm hhm => ⟨(hparams hm hhm).1.ne', (hparams hm hhm).2.ne'⟩) hlen.le]
    omega
  · exact powerPolynomial_leadingCoeff_pos k params hparams hlen.le
  · exact hz

theorem powerPolynomial_eval_strictMonoOn (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0 < hm.1 ∧ 0 < hm.2) (hlen : params.length < k) :
    StrictMonoOn (powerPolynomial k params).eval (Set.Ici 0) := by
  apply eval_strictMonoOn _ (fun i => powerPolynomial_coeff_nonneg k params
    (fun hm hhm => ⟨(hparams hm hhm).1.le, (hparams hm hhm).2⟩) i)
  · rw [powerPolynomial_natDegree k params
      (fun hm hhm => ⟨(hparams hm hhm).1.ne', (hparams hm hhm).2.ne'⟩) hlen.le]
    omega
  · exact powerPolynomial_leadingCoeff_pos k params hparams hlen.le

theorem powerPolynomial_eval_injOn (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0 < hm.1 ∧ 0 < hm.2) (hlen : params.length < k) :
    Set.InjOn (powerPolynomial k params).eval (Set.Ici 0) :=
  (powerPolynomial_eval_strictMonoOn k params hparams hlen).injOn

#print axioms powerPolynomial_coeff_nonneg
#print axioms powerPolynomial_real_nonnegative
#print axioms powerPolynomial_leadingCoeff_pos
#print axioms powerPolynomial_derivative_eval_pos
#print axioms powerPolynomial_eval_injOn
end Waring.PolicyCompletionPositivePhase
