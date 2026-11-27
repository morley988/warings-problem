import Waring.PolicyCompletionPolynomialContent
import Waring.FiniteFieldMordellBound

/-! # A fixed-degree prime-field base for the polynomial prime-power recursion -/

noncomputable section
namespace Waring.PolicyCompletionPolynomialPrime
open Polynomial PolicyCompletionPolynomialContent

def huaConstant (D : ℕ) : ℝ := 2*((D : ℝ)+1)^(D+2)+2

theorem huaConstant_ge_two (D : ℕ) : 2 ≤ huaConstant D := by
  unfold huaConstant
  have h : 0 ≤ 2*((D : ℝ)+1)^(D+2) := by positivity
  linarith

theorem huaConstant_pos (D : ℕ) : 0 < huaConstant D :=
  (by norm_num : (0 : ℝ)<2).trans_le (huaConstant_ge_two D)

theorem huaConstant_ge_degree_square (D : ℕ) : (D : ℝ)^2 ≤ huaConstant D := by
  have hpow : ((D : ℝ)+1)^2 ≤ ((D : ℝ)+1)^(D+2) :=
    pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) D; linarith) (by omega)
  have hbase : (D : ℝ)^2 ≤ ((D : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) D]
  unfold huaConstant
  nlinarith [pow_nonneg (show (0 : ℝ)≤D+1 by positivity) (D+2)]

theorem prime_polynomial_bound_fixed_degree {p D : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (hf : 1 ≤ f.natDegree) (hfD : f.natDegree ≤ D)
    (hDp : D < p) :
    ‖FiniteFieldMordell.polynomialSum p f‖ ≤
      huaConstant D*(p : ℝ)^(1-1/(f.natDegree : ℝ)) := by
  by_cases hf1 : f.natDegree=1
  · rw [FiniteFieldMordell.polynomialSum_linear f hf1,norm_zero]
    exact mul_nonneg (huaConstant_pos D).le (by positivity)
  have hf2 : 2 ≤ f.natDegree := by omega
  have hbound := FiniteFieldMordell.polynomialSum_mordell f hf2 (hfD.trans_lt hDp)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hd : (1 : ℝ) ≤ f.natDegree := by exact_mod_cast hf
  have hbase : 1 ≤ 2*(f.natDegree : ℝ)^(f.natDegree+1) := by
    have hh := one_le_pow₀ hd (n := f.natDegree+1)
    linarith
  have hinv : (2*(f.natDegree : ℝ))⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    linarith
  calc
    _ ≤ 2*(f.natDegree : ℝ)^(f.natDegree+1) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hinv
    _ ≤ 2*((D : ℝ)+1)^(D+2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ ((D : ℝ)+1)^(f.natDegree+1) := pow_le_pow_left₀ (Nat.cast_nonneg _)
          (by exact_mod_cast (show f.natDegree ≤ D+1 by omega)) _
        _ ≤ _ := pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) D; linarith) (by omega)
    _ ≤ _ := by unfold huaConstant; linarith

theorem nonconstantPrimitiveAt_map_natDegree_pos {p : ℕ} {f : Polynomial ℤ}
    (hf : NonconstantPrimitiveAt p f) :
    0 < (f.map (Int.castRingHom (ZMod p))).natDegree := by
  obtain ⟨i,hi,hci⟩ := hf
  apply hi.trans_le
  apply Polynomial.le_natDegree_of_ne_zero
  rw [Polynomial.coeff_map]
  change (f.coeff i : ZMod p) ≠ 0
  exact mt (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hci

theorem good_prime_content_eq_zero {p D : ℕ} [Fact p.Prime]
    (f F : Polynomial ℤ) (t : ℕ) (hf : NonconstantPrimitiveAt p f)
    (hder : f.derivative=C ((p : ℤ)^t)*F) (hfD : f.natDegree ≤ D) (hDp : D < p) :
    t=0 := by
  have hpow := (derivative_content_pow_le_degree f F t hf hder).trans hfD
  by_contra ht
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpt : p ≤ p^t := Nat.le_of_dvd (pow_pos hp _) (dvd_pow_self p ht)
  omega

/-- Below the characteristic, differentiation lowers the actual reduced
degree by exactly one. -/
theorem derivative_natDegree_add_one {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (hf : 0 < f.natDegree) (hfp : f.natDegree < p) :
    f.derivative.natDegree+1=f.natDegree := by
  have hcast : (f.natDegree : ZMod p) ≠ 0 := by
    rw [ne_eq,ZMod.natCast_eq_zero_iff]
    exact fun hd => (Nat.not_le_of_lt hfp) (Nat.le_of_dvd hf hd)
  have hcoeff : f.derivative.coeff (f.natDegree-1) ≠ 0 := by
    rw [Polynomial.coeff_derivative,Nat.sub_add_cancel hf]
    have hc : f.coeff f.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hf)
    have he : ((f.natDegree-1 : ℕ) : ZMod p)+1=(f.natDegree : ZMod p) := by
      simpa only [Nat.cast_add,Nat.cast_one] using
        congrArg (fun n : ℕ => (n : ZMod p)) (Nat.sub_add_cancel hf)
    rw [he]
    exact mul_ne_zero hc hcast
  have hlo := Polynomial.le_natDegree_of_ne_zero hcoeff
  have hhi := Polynomial.natDegree_derivative_lt hf.ne'
  omega

#print axioms prime_polynomial_bound_fixed_degree
#print axioms good_prime_content_eq_zero
#print axioms derivative_natDegree_add_one
end Waring.PolicyCompletionPolynomialPrime
