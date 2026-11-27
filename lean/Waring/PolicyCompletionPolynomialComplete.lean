import Waring.PolicyCompletionPolynomialCRT
import Waring.PolicyCompletionRoots

/-! # The actual composite-modulus complete polynomial estimate

CRT contributes one fixed degree constant per distinct prime. The proved
divisor estimate absorbs this into an arbitrary small power of q, while
the common coefficient gcd is retained exactly.
-/

noncomputable section
namespace Waring.PolicyCompletionPolynomialComplete
open Polynomial PolicyCompletionPolynomialResidues PolicyCompletionPolynomialGcd
  PolicyCompletionPolynomialPrimePower PolicyCompletionPolynomialCRT

theorem polynomial_sum_divisor_bound (D : ℕ) (hD : 1 ≤ D)
    (q : ℕ) [NeZero q] (f : Polynomial ℤ) (hfD : f.natDegree ≤ D)
    (B : ℕ) (hB : CoefficientDivisorBoundAt q f B) :
    ‖integerPolynomialSum q f‖ ≤
      (q.divisors.card : ℝ)^(⌈completeSumConstant D⌉₊)*
        (q : ℝ)^(1-1/(D : ℝ))*(Nat.gcd q B : ℝ)^(1/(D : ℝ)) := by
  let N := ⌈completeSumConstant D⌉₊
  have hC := completeSumConstant_pos hD
  have hCN : completeSumConstant D ≤ (N : ℝ) := Nat.le_ceil _
  have hc : N^q.primeFactors.card ≤ q.divisors.card^N := by
    calc
      _ ≤ (2^N)^q.primeFactors.card := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = (2^q.primeFactors.card)^N := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left
        (PolicyCompletionRoots.two_pow_primeFactors_card_le_divisors
          (Nat.pos_of_ne_zero (NeZero.ne q))) _
  have hcReal : (completeSumConstant D)^q.primeFactors.card ≤ (q.divisors.card : ℝ)^N := by
    apply (pow_le_pow_left₀ hC.le hCN _).trans
    exact_mod_cast hc
  apply (polynomial_sum_omega_bound D hD q f hfD B hB).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right hcReal (by positivity)

/-- A uniform Hua bound for the literal complete sum of any integer
polynomial, including arbitrary constant and linear terms and all moduli. -/
theorem integerPolynomialSum_le_rpow (D : ℕ) (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (q : ℕ) [NeZero q] (f : Polynomial ℤ),
      f.natDegree ≤ D → ∀ B : ℕ,CoefficientDivisorBoundAt q f B →
      ‖integerPolynomialSum q f‖ ≤
        C*(q : ℝ)^(1-1/(D : ℝ)+ε)*(Nat.gcd q B : ℝ)^(1/(D : ℝ)) := by
  obtain ⟨C,hC,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow
    (⌈completeSumConstant D⌉₊) hε
  refine ⟨C,hC,?_⟩
  intro q _ f hfD B hB
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  calc
    _ ≤ (q.divisors.card : ℝ)^(⌈completeSumConstant D⌉₊)*
        (q : ℝ)^(1-1/(D : ℝ))*(Nat.gcd q B : ℝ)^(1/(D : ℝ)) :=
      polynomial_sum_divisor_bound D hD q f hfD B hB
    _ ≤ (C*(q : ℝ)^ε)*(q : ℝ)^(1-1/(D : ℝ))*(Nat.gcd q B : ℝ)^(1/(D : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hdiv q hq) (by positivity)
    _ = _ := by
      rw [mul_assoc C,← Real.rpow_add hqR,add_comm ε (1-1/(D : ℝ))]

/-- Keeping any two positive-index coefficients gives the gcd needed for
an auxiliary polynomial with an arbitrary linear completion twist. -/
theorem integerPolynomialSum_le_coefficient_gcd (D : ℕ) (hD : 1 ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (q : ℕ) [NeZero q] (f : Polynomial ℤ),
      f.natDegree ≤ D → ∀ i j : ℕ,0 < i → 0 < j →
      ‖integerPolynomialSum q f‖ ≤
        C*(q : ℝ)^(1-1/(D : ℝ)+ε)*
          (Nat.gcd q (Nat.gcd (f.coeff i).natAbs (f.coeff j).natAbs) : ℝ)^(1/(D : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := integerPolynomialSum_le_rpow D hD hε
  refine ⟨C,hC,?_⟩
  intro q _ f hfD i j hi hj
  exact hbound q f hfD _ (coefficientDivisorBoundAt_gcd q f i j hi hj)

#print axioms integerPolynomialSum_le_rpow
#print axioms integerPolynomialSum_le_coefficient_gcd
end Waring.PolicyCompletionPolynomialComplete
