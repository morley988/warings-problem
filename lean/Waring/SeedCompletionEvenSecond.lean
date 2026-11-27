import Waring.FirstDifferenceSecond
import Waring.IntegerDifferenceDegree
import Waring.SeedCompletionCurveUniform

/-!
# Positive even-degree second differences with second coefficient one

The finite positive binomial expansion represents the actual normalized
second difference. Its center polynomial is even and strictly increasing
on positive centers; varying the first coefficient changes that polynomial.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenSecond
open IntegerDifferencePolynomial Polynomial FirstDifferenceSecond

def exponent (d i j : ℕ) : ℕ := 2*d-(2*i+1)-(2*j+1)

def coefficient (d h m a i j : ℕ) : ℕ :=
  4*(2*d).choose (2*i+1)*(2*d-(2*i+1)).choose (2*j+1)*
    h^(2*i+1)*a^(2*j+1)*m^(2*d*(2*i))

def phase (d h m a z : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range (d-i),
    coefficient d h m a i j*z^(exponent d i j)

def phasePolynomial (d h m a : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range (d-i),
    monomial (exponent d i j) ((coefficient d h m a i j : ℕ) : ℤ)

def realPolynomial (d h m a : ℕ) : Polynomial ℝ :=
  (phasePolynomial d h m a).map (Int.castRingHom ℝ)

theorem phasePolynomial_eval (d h m a z : ℕ) :
    (phasePolynomial d h m a).eval (z : ℤ)=(phase d h m a z : ℤ) := by
  simp [phasePolynomial,phase,Polynomial.eval_finset_sum,Polynomial.eval_monomial]

theorem realPolynomial_eval (d h m a z : ℕ) :
    (realPolynomial d h m a).eval (z : ℝ)=(phase d h m a z : ℝ) := by
  unfold realPolynomial
  rw [Polynomial.eval_map]
  have H := congrArg (fun n : ℤ => (n : ℝ)) (phasePolynomial_eval d h m a z)
  change (Int.castRingHom ℝ) ((phasePolynomial d h m a).eval (z : ℤ)) = _ at H
  rw [← Polynomial.eval₂_at_apply] at H
  simpa only [Int.cast_natCast] using H

theorem coefficient_zero_zero (d h m a : ℕ) :
    coefficient d h m a 0 0=4*(2*d)*(2*d-1)*h*a := by
  simp [coefficient]

theorem phase_pos {d h m a z : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) (hz : 0 < z) : 0 < phase d h m a z := by
  unfold phase
  apply Finset.sum_pos'
  · intro i hi
    exact Nat.zero_le _
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_pos'
    · intro j hj
      exact Nat.zero_le _
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      rw [coefficient_zero_zero]
      have hk : 0 < 2*d-1 := by omega
      positivity

theorem height_dvd (d h m a z : ℕ) : h ∣ phase d h m a z := by
  unfold phase
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self h (by omega : 2*i+1 ≠ 0)) _

theorem secondHeight_dvd (d h m a z : ℕ) : a ∣ phase d h m a z := by
  unfold phase
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self a (by omega : 2*j+1 ≠ 0)) _

/-- Strict center monotonicity, including the endpoint zero. -/
theorem phase_center_strictMono {d h m a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) : StrictMono (fun z => phase d h m a z) := by
  intro z w hzw
  unfold phase
  apply Finset.sum_lt_sum
  · intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_lt_sum
    · intro j hj
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      rw [coefficient_zero_zero]
      have hc : 0 < 4*(2*d)*(2*d-1)*h*a := by
        have hk : 0 < 2*d-1 := by omega
        positivity
      exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hzw
        (by unfold exponent; omega)) hc

/-- The remaining coefficient is strictly determined at any positive center. -/
theorem phase_coefficient_strictMono {d h a z : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) (hz : 0 < z) :
    StrictMono (fun m => phase d h m a z) := by
  intro m n hmn
  unfold phase
  apply Finset.sum_lt_sum
  · intro i hi
    apply Finset.sum_le_sum
    intro j hj
    unfold coefficient
    gcongr
  · refine ⟨1,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_lt_sum
    · intro j hj
      unfold coefficient
      gcongr
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      unfold coefficient
      have hc1 : 0 < (2*d).choose (2*1+1) := Nat.choose_pos (by omega)
      have hc2 : 0 < (2*d-(2*1+1)).choose (2*0+1) := Nat.choose_pos (by omega)
      apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
      apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
      exact Nat.pow_lt_pow_left hmn (by omega)

/-- The support has the correct reduced degree. -/
theorem phasePolynomial_natDegree_le (d h m a : ℕ) :
    (phasePolynomial d h m a).natDegree ≤ 2*d-2 := by
  unfold phasePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by unfold exponent; omega)

/-- The even center powers hold exactly, without a restriction on coefficients. -/
theorem realPolynomial_even (d h m a : ℕ) (t : ℝ) :
    (realPolynomial d h m a).eval (-t)=(realPolynomial d h m a).eval t := by
  unfold realPolynomial phasePolynomial
  simp only [Polynomial.map_sum,Polynomial.eval_finset_sum,map_monomial,eval_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi := Finset.mem_range.mp hi
  have hj := Finset.mem_range.mp hj
  have he : exponent d i j=2*(d-i-j-1) := by unfold exponent; omega
  rw [he,pow_mul,pow_mul]
  simp

/-- Distinct first coefficients produce different complete center polynomials. -/
theorem realPolynomial_injective {d h a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) : Function.Injective (fun m => realPolynomial d h m a) := by
  intro m n heq
  have he := congrArg (fun p : Polynomial ℝ => p.eval 1) heq
  have hm := realPolynomial_eval d h m a 1
  have hn := realPolynomial_eval d h n a 1
  norm_num only [Nat.cast_one] at hm hn
  dsimp only at he
  rw [hm,hn] at he
  exact (phase_coefficient_strictMono hd hh ha (by norm_num : 0 < 1)).injective
    (by exact_mod_cast he)

theorem phasePolynomial_coeff_top {d : ℕ} (hd : 2 ≤ d) (h m a : ℕ) :
    (phasePolynomial d h m a).coeff (2*d-2)=
      ((4*(2*d)*(2*d-1)*h*a : ℕ) : ℤ) := by
  unfold phasePolynomial
  simp only [finset_sum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · rw [show exponent d 0 0=2*d-2 by unfold exponent; omega,
        coeff_monomial,if_pos rfl,coefficient_zero_zero]
    · intro j hj hj0
      rw [coeff_monomial,if_neg]
      unfold exponent
      omega
    · intro hbad
      exact False.elim (hbad (Finset.mem_range.mpr (by omega)))
  · intro i hi hi0
    apply Finset.sum_eq_zero
    intro j hj
    rw [coeff_monomial,if_neg]
    unfold exponent
    omega
  · intro hbad
    exact False.elim (hbad (Finset.mem_range.mpr (by omega)))

theorem phasePolynomial_natDegree {d h m a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) :
    (phasePolynomial d h m a).natDegree=2*d-2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (phasePolynomial_natDegree_le d h m a)
  rw [phasePolynomial_coeff_top hd]
  have hk : 0 < 2*d-1 := by omega
  positivity

theorem phasePolynomial_leadingCoeff {d h m a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) :
    (phasePolynomial d h m a).leadingCoeff=((4*(2*d)*(2*d-1)*h*a : ℕ) : ℤ) := by
  rw [leadingCoeff,phasePolynomial_natDegree hd hh ha,phasePolynomial_coeff_top hd]

theorem realPolynomial_natDegree {d h m a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) :
    (realPolynomial d h m a).natDegree=2*d-2 := by
  rw [realPolynomial,natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),
    phasePolynomial_natDegree hd hh ha]

theorem realPolynomial_leadingCoeff {d h m a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) :
    (realPolynomial d h m a).leadingCoeff=((4*(2*d)*(2*d-1)*h*a : ℕ) : ℝ) := by
  rw [realPolynomial,leadingCoeff_map' (Int.cast_injective (α := ℝ)),
    phasePolynomial_leadingCoeff hd hh ha]
  rfl

/- The supported even degrees are identified with the exact four-term
centered difference before the one normalizing division. -/
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem phase_mul_identity {d : ℕ} (hd : supportedHalfDegree d) (h m a z : ℕ) :
    (m : ℤ)^(2*d)*(phase d h m a z : ℤ) =
      (((z : ℤ)+(a : ℤ)+(h : ℤ)*(m : ℤ)^(2*d))^(2*d) -
        ((z : ℤ)+(a : ℤ)-(h : ℤ)*(m : ℤ)^(2*d))^(2*d)) -
      (((z : ℤ)-(a : ℤ)+(h : ℤ)*(m : ℤ)^(2*d))^(2*d) -
        ((z : ℤ)-(a : ℤ)-(h : ℤ)*(m : ℤ)^(2*d))^(2*d)) := by
  rcases hd with rfl | rfl | rfl <;>
    norm_num [phase,coefficient,exponent,Finset.sum_range_succ,Nat.choose] <;> ring

theorem first_mul_identity (k : ℕ) (h m z : ℤ) :
    m^k*(powerPolynomial k [(h,m)]).eval z=(z+h*m^k)^k-(z-h*m^k)^k := by
  have H := congrArg (fun p : Polynomial ℤ => p.eval z)
    (difference_mul k h m (Polynomial.X^k))
  simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X] using H

theorem phase_eq_powerPolynomial {d : ℕ} (hd : supportedHalfDegree d)
    (h m a z : ℕ) (hm : 0 < m) :
    (phase d h m a z : ℤ)=
      (powerPolynomial (2*d) [((a : ℤ),1),((h : ℤ),(m : ℤ))]).eval (z : ℤ) := by
  have hm0 : (m : ℤ)^(2*d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  apply mul_left_cancel₀ hm0
  rw [phase_mul_identity hd]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul (2*d) (a : ℤ) 1 (powerPolynomial (2*d) [((h : ℤ),(m : ℤ))]))
  have H' : (powerPolynomial (2*d) [((a : ℤ),1),((h : ℤ),(m : ℤ))]).eval (z : ℤ) =
      (powerPolynomial (2*d) [((h : ℤ),(m : ℤ))]).eval ((z : ℤ)+(a : ℤ)) -
      (powerPolynomial (2*d) [((h : ℤ),(m : ℤ))]).eval ((z : ℤ)-(a : ℤ)) := by
    simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,one_pow,mul_one,one_mul] using H
  rw [H',mul_sub,first_mul_identity,first_mul_identity]

#print axioms phase_center_strictMono
#print axioms phase_coefficient_strictMono
#print axioms realPolynomial_even
#print axioms phase_eq_powerPolynomial
end Waring.SeedCompletionEvenSecond
