import Waring.PolicyCompletionPolynomialContentSum

/-! # Prime-power polynomial bounds with the actual coefficient gcd loss -/

noncomputable section
namespace Waring.PolicyCompletionPolynomialGcd
open Polynomial PolicyCompletionPolynomialRecursion PolicyCompletionPolynomialContent
  PolicyCompletionPolynomialResidues PolicyCompletionPolynomialPrimePower
  PolicyCompletionPolynomialContentSum PolicyCompletionPolynomialHuaBounds

/-- B bounds the common divisors of the nonconstant coefficients which
also divide q. This purely finite arithmetic condition is stable under
unit scalar twists modulo q. -/
def CoefficientDivisorBoundAt (q : ℕ) (f : Polynomial ℤ) (B : ℕ) : Prop :=
  ∀ d : ℕ,d ∣ q → (∀ i : ℕ,0 < i → (d : ℤ) ∣ f.coeff i) → d ∣ B

theorem coefficientDivisorBoundAt_coefficient (q : ℕ) (f : Polynomial ℤ)
    (i : ℕ) (hi : 0 < i) : CoefficientDivisorBoundAt q f (f.coeff i).natAbs := by
  intro d hd hcoeff
  exact Int.natCast_dvd.mp (hcoeff i hi)

theorem coefficientDivisorBoundAt_gcd (q : ℕ) (f : Polynomial ℤ)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    CoefficientDivisorBoundAt q f (Nat.gcd (f.coeff i).natAbs (f.coeff j).natAbs) := by
  intro d hd hcoeff
  exact Nat.dvd_gcd (Int.natCast_dvd.mp (hcoeff i hi)) (Int.natCast_dvd.mp (hcoeff j hj))

theorem coefficientDivisorBoundAt_of_dvd {q n B : ℕ} {f : Polynomial ℤ}
    (h : CoefficientDivisorBoundAt q f B) (hnq : n ∣ q) : CoefficientDivisorBoundAt n f B :=
  fun d hdn hd => h d (hdn.trans hnq) hd

theorem coefficientDivisorBoundAt_unit_mul {q B : ℕ} {f : Polynomial ℤ} {u : ℤ}
    (h : CoefficientDivisorBoundAt q f B) (hu : IsCoprime (q : ℤ) u) :
    CoefficientDivisorBoundAt q (C u*f) B := by
  intro d hd hcoeff
  apply h d hd
  intro i hi
  have hdu : IsCoprime (d : ℤ) u := hu.of_isCoprime_of_dvd_left (by exact_mod_cast hd)
  apply hdu.dvd_of_dvd_mul_left
  simpa only [Polynomial.coeff_C_mul] using hcoeff i hi

/-- The prime-power bound includes all coefficient contents and every
constant phase. No coprimality or nonconstant-phase assumption remains. -/
theorem polynomial_primepower_gcd_bound {p D : ℕ} [Fact p.Prime]
    (hD : 1 ≤ D) (m : ℕ) (f : Polynomial ℤ) (hfD : f.natDegree ≤ D)
    (B : ℕ) (hB : CoefficientDivisorBoundAt (p^m) f B) :
    ‖integerPolynomialSum (p^m) f‖ ≤
      completeSumConstant D*((p^m : ℕ) : ℝ)^(1-1/(D : ℝ))*
        (Nat.gcd (p^m) B : ℝ)^(1/(D : ℝ)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < p^m := pow_pos hp m
  have hqR : 0 < ((p^m : ℕ) : ℝ) := by exact_mod_cast hq
  have hDreal : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  by_cases hf0 : f.natDegree=0
  · have hqB : p^m ∣ B := by
      apply hB (p^m) dvd_rfl
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact dvd_zero _
    rw [Nat.gcd_eq_left hqB,mul_assoc,← Real.rpow_add hqR,
      show (1-1/(D : ℝ))+1/(D : ℝ)=1 by ring,Real.rpow_one]
    exact (norm_integerPolynomialSum_le _ _).trans
      (le_mul_of_one_le_left hqR.le (completeSumConstant_ge_one hD))
  obtain ⟨v,g,he,hg,hgdeg⟩ := exists_nonconstantPrimitive_factor (p := p) f (Nat.pos_of_ne_zero hf0)
  have hdivq : p^(min v m) ∣ p^m := pow_dvd_pow p (min_le_right _ _)
  have hcoeff : ∀ i : ℕ,0 < i → ((p^(min v m) : ℕ) : ℤ) ∣ f.coeff i := by
    intro i hi
    rw [he,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_C,
      if_neg hi.ne',add_zero]
    have hdiv : ((p^(min v m) : ℕ) : ℤ) ∣ (p : ℤ)^v := by
      simpa only [Nat.cast_pow] using pow_dvd_pow (p : ℤ) (min_le_left v m)
    exact hdiv.trans (dvd_mul_right _ _)
  have hdivB := hB (p^(min v m)) hdivq hcoeff
  have hdivgcd := Nat.dvd_gcd hdivq hdivB
  have hgcdpos : 0 < Nat.gcd (p^m) B := Nat.gcd_pos_of_pos_left B hq
  have hpowgcd : (p^(min v m) : ℕ) ≤ Nat.gcd (p^m) B := Nat.le_of_dvd hgcdpos hdivgcd
  rw [he]
  apply (polynomial_primepower_content_bound m v g hg (hgdeg.trans hfD) (f.eval 0)).trans
  have hCpos := completeSumConstant_pos hD
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hpowgcd) (by positivity)

#print axioms polynomial_primepower_gcd_bound
end Waring.PolicyCompletionPolynomialGcd
