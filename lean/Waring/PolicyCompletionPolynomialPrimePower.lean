import Waring.PolicyCompletionPolynomialHua

/-! # Uniform actual Hua cancellation at every prime power -/

noncomputable section
namespace Waring.PolicyCompletionPolynomialPrimePower
open Polynomial PolicyCompletionPolynomialRecursion PolicyCompletionPolynomialContent
  PolicyCompletionPolynomialResidues PolicyCompletionPolynomialPrime
  PolicyCompletionPolynomialHuaBounds PolicyCompletionPolynomialHua

def completeSumConstant (D : ℕ) : ℝ := (D : ℝ)*(huaConstant D)^D

theorem completeSumConstant_pos {D : ℕ} (hD : 1 ≤ D) : 0 < completeSumConstant D := by
  unfold completeSumConstant
  exact mul_pos (by exact_mod_cast (show 0 < D by omega)) (pow_pos (huaConstant_pos D) _)

theorem completeSumConstant_ge_one {D : ℕ} (hD : 1 ≤ D) : 1 ≤ completeSumConstant D := by
  unfold completeSumConstant
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD)
    (one_le_pow₀ (by have h := huaConstant_ge_two D; linarith))

/-- Every nonconstant primitive polynomial of degree at most D has the
Hua exponent, uniformly over all primes and every prime-power level. -/
theorem primitive_polynomial_primepower_bound {p D : ℕ} [Fact p.Prime]
    (m : ℕ) (f : Polynomial ℤ) (hf : NonconstantPrimitiveAt p f)
    (hfD : f.natDegree ≤ D) :
    ‖integerPolynomialSum (p^m) f‖ ≤
      completeSumConstant D*((p^m : ℕ) : ℝ)^(1-1/(D : ℝ)) := by
  have hfpos := nonconstantPrimitiveAt_natDegree_pos hf
  have hDpos : 0 < D := hfpos.trans_le hfD
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpInt : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hpp : 0 < (p : ℝ) := zero_lt_one.trans_le hpr
  obtain ⟨t,F,hder,hF⟩ := exists_primitiveAt_factor (p := p) f.derivative
    (nonconstantPrimitiveAt_derivative_ne_zero hf)
  let e := (F.map (Int.castRingHom (ZMod p))).natDegree
  have hFdeg : F.natDegree ≤ D-1 := by
    have hh := Polynomial.natDegree_derivative_le f
    rw [hder,Polynomial.natDegree_C_mul (pow_ne_zero t hpInt)] at hh
    exact hh.trans (Nat.sub_le_sub_right hfD 1)
  have he : e+1 ≤ D := by
    have hmap : e ≤ F.natDegree := Polynomial.natDegree_map_le
    omega
  have hereal : (e : ℝ)+1 ≤ (D : ℝ) := by exact_mod_cast he
  have heden : (0 : ℝ) < (e : ℝ)+1 := by positivity
  have hfracm : (m : ℝ)/(D : ℝ) ≤ (m : ℝ)/((e : ℝ)+1) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg m) heden hereal
  have hfract : (t : ℝ)/((e : ℝ)+1) ≤ (t : ℝ) := by
    apply (div_le_iff₀ heden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) e,Nat.cast_nonneg (α := ℝ) t]
  have hexp : huaExponent m t e ≤ (m : ℝ)*(1-1/(D : ℝ))+(t : ℝ) := by
    unfold huaExponent
    rw [sub_div]
    simp only [div_eq_mul_inv,one_mul] at hfracm hfract ⊢
    nlinarith
  have hK := huaConstant_ge_two D
  have hcoef : (huaConstant D)^(e+1) ≤ (huaConstant D)^D :=
    pow_le_pow_right₀ (by linarith) he
  have hpt : (p : ℝ)^t ≤ (D : ℝ) := by
    exact_mod_cast (derivative_content_pow_le_degree f F t hf hder).trans hfD
  have hscale : ((p^m : ℕ) : ℝ)^(1-1/(D : ℝ))=
      (p : ℝ)^((m : ℝ)*(1-1/(D : ℝ))) := by
    rw [Nat.cast_pow,Real.rpow_mul hpp.le,Real.rpow_natCast]
  calc
    _ ≤ (huaConstant D)^(e+1)*(p : ℝ)^(huaExponent m t e) :=
      integerPolynomialSum_hua_internal m f F t hf hfD hder hF
    _ ≤ (huaConstant D)^D*(p : ℝ)^((m : ℝ)*(1-1/(D : ℝ))+(t : ℝ)) := by
      apply mul_le_mul hcoef (Real.rpow_le_rpow_of_exponent_le hpr hexp)
        (by positivity) (by positivity)
    _ = (huaConstant D)^D*(p : ℝ)^((m : ℝ)*(1-1/(D : ℝ)))*(p : ℝ)^t := by
      rw [Real.rpow_add hpp,Real.rpow_natCast]
      ring
    _ ≤ (huaConstant D)^D*(p : ℝ)^((m : ℝ)*(1-1/(D : ℝ)))*(D : ℝ) :=
      mul_le_mul_of_nonneg_left hpt (by positivity)
    _ = _ := by rw [hscale,completeSumConstant]; ring

#print axioms primitive_polynomial_primepower_bound
end Waring.PolicyCompletionPolynomialPrimePower
