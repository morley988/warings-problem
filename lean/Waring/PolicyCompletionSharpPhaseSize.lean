import Waring.PolicyCompletionPhaseContent

/-!
# Sharp derivative size for the actual centered phase

Each normalized centered difference contributes its actual height factor
and lowers the degree. A monomial difference estimate proves this directly,
so the bound retains prod(h), unlike a coarse triangle-inequality bound.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionSharpPhaseSize
open Polynomial IntegerDifferencePolynomial PolicyCompletionPositivePhase
open PolicyCompletionPolynomialDiscrete PolicyCompletionPhaseContent

theorem eval_centered_sub_le (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    {z a : ℝ} (hz : 0≤z) (ha : 0≤a) :
    f.eval (z+a)-f.eval (z-a) ≤ 2*a*f.derivative.eval (z+a) := by
  have hmono (i : ℕ) : (z+a)^i-(z-a)^i ≤ 2*a*(i:ℝ)*(z+a)^(i-1) := by
    have hh := abs_pow_sub_pow_le (a := z+a) (b := z-a) (n := i)
    have habs : |z-a|≤z+a := by
      simpa only [abs_of_nonneg hz, abs_of_nonneg ha] using abs_sub z a
    rw [abs_of_nonneg (add_nonneg hz ha), max_eq_left habs,
      show z+a-(z-a)=2*a by ring, abs_of_nonneg (mul_nonneg (by norm_num) ha)] at hh
    exact (le_abs_self _).trans hh
  rw [Polynomial.derivative_eval]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_left (hmono i) (hf i)
  nlinarith

theorem difference_eval_le (k : ℕ) {h m : ℤ} (hh : 0≤h) (hm : 0<m)
    (f : Polynomial ℤ) (hf : ∀ i, 0≤f.coeff i) {z : ℝ} (hz : 0≤z) :
    ((difference k h m f).map (Int.castRingHom ℝ)).eval z ≤
      2*(h:ℝ)*((f.derivative).map (Int.castRingHom ℝ)).eval (z+(h:ℝ)*(m:ℝ)^k) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hhR : (0:ℝ)≤h := by exact_mod_cast hh
  have hfR : NonnegativeCoefficients (f.map (Int.castRingHom ℝ)) := by
    intro i
    rw [Polynomial.coeff_map]
    change 0≤((f.coeff i:ℤ):ℝ)
    exact_mod_cast hf i
  have hmain := eval_centered_sub_le (f.map (Int.castRingHom ℝ)) hfR hz
    (mul_nonneg hhR (pow_nonneg hmR.le k))
  rw [Polynomial.eval_map, difference_eval_real k h m f hm.ne']
  have hdiv := div_le_div_of_nonneg_right hmain (pow_nonneg hmR.le k)
  simp only [Polynomial.derivative_map, Polynomial.eval_map] at hdiv
  apply hdiv.trans_eq
  rw [Polynomial.eval_map]
  field_simp

theorem iterate_derivative_difference (k : ℕ) (h m : ℤ) (f : Polynomial ℤ)
    (hm : m≠0) (r : ℕ) :
    (derivative^[r]) (difference k h m f) = difference k h m ((derivative^[r]) f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply', ih, derivative_difference k h m _ hm]

theorem iterate_derivative_coeff_nonneg (f : Polynomial ℤ) (hf : ∀ i, 0≤f.coeff i)
    (r i : ℕ) : 0≤((derivative^[r]) f).coeff i := by
  rw [Polynomial.coeff_iterate_derivative]
  exact mul_nonneg (Nat.cast_nonneg _) (hf _)

theorem source_iterated_derivative_bound (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0<hm.1 ∧ 0<hm.2)
    (r : ℕ) (hr : r+params.length≤k) {z : ℝ} (hz : 0≤z) :
    (((derivative^[r]) (powerPolynomial k params)).map (Int.castRingHom ℝ)).eval z ≤
      (2:ℝ)^params.length*(heightProduct params:ℝ)*
        (k.descFactorial (r+params.length):ℝ)*(z+shiftRadius k params)^(k-(r+params.length)) := by
  induction params generalizing r z with
  | nil =>
    simp [powerPolynomial, heightProduct, shiftRadius, Polynomial.iterate_derivative_X_pow_eq_C_mul,
      Polynomial.eval_map, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
      Polynomial.eval₂_X]
  | cons p rest ih =>
    have hp := hparams p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, 0<q.1 ∧ 0<q.2 :=
      fun q hq => hparams q (List.mem_cons_of_mem _ hq)
    have hpH : (0:ℝ)<p.1 := by exact_mod_cast hp.1
    have hpM : (0:ℝ)<p.2 := by exact_mod_cast hp.2
    have hr' : (r+1)+rest.length≤k := by simp only [List.length_cons] at hr; omega
    have hposcoeff : ∀ i, 0≤((derivative^[r]) (powerPolynomial k rest)).coeff i :=
      fun i => iterate_derivative_coeff_nonneg _
        (fun j => powerPolynomial_coeff_nonneg k rest (fun q hq => ⟨(hrest q hq).1.le,(hrest q hq).2⟩) j) r i
    have hfirst := difference_eval_le k hp.1.le hp.2
      ((derivative^[r]) (powerPolynomial k rest)) hposcoeff hz
    have hnext := ih hrest (r+1) hr' (add_nonneg hz (by positivity : 0≤(p.1:ℝ)*(p.2:ℝ)^k))
    rw [Function.iterate_succ_apply'] at hnext
    rw [powerPolynomial, iterate_derivative_difference k p.1 p.2 _ hp.2.ne' r]
    apply hfirst.trans
    apply (mul_le_mul_of_nonneg_left hnext (by positivity : 0≤2*(p.1:ℝ))).trans_eq
    have hindex : r+(rest.length+1)=(r+1)+rest.length := by omega
    simp only [heightProduct, List.map_cons, List.prod_cons, List.length_cons, pow_succ,
      Int.cast_mul, shiftRadius, List.sum_cons, abs_of_pos hpH, abs_of_pos hpM, hindex]
    ring

theorem source_derivative_bound (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0<hm.1 ∧ 0<hm.2)
    (hlen : params.length<k) {z : ℝ} (hz : 0≤z) :
    ((powerPolynomial k params).map (Int.castRingHom ℝ)).derivative.eval z ≤
      (2:ℝ)^params.length*(heightProduct params:ℝ)*
        (k.descFactorial (params.length+1):ℝ)*(z+shiftRadius k params)^(k-(params.length+1)) := by
  simpa only [Function.iterate_one, ← Polynomial.derivative_map, Nat.add_comm 1 params.length] using
    source_iterated_derivative_bound k params hparams 1 (by omega) hz

#print axioms source_iterated_derivative_bound
#print axioms source_derivative_bound
end Waring.PolicyCompletionSharpPhaseSize
