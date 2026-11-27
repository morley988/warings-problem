import Waring.PolicyCompletionPolynomialBroad
import Waring.PolicyCompletionPolynomialDecay

/-! # Broad rational approximation for the literal source difference phase -/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionSourceMajor
open Polynomial QuadraticModulation EndgameCompletion IntegerDifferencePolynomial
open PolicyCompletionPositivePhase PolicyCompletionPhaseContent PolicyCompletionPolynomialBroad
open PolicyCompletionPolynomialFourier PolicyCompletionPolynomialResidues
open PolicyCompletionPolynomialCalculus

def integerPolynomialWeyl (f : Polynomial ℤ) (P α : ℝ) : ℂ :=
  ∑ n ∈ ordinaryNumbers P, e (α*(f.map (Int.castRingHom ℝ)).eval (n:ℝ))

theorem integerPolynomialWeyl_rational (q : ℕ) [NeZero q] (a : ℤ)
    (f : Polynomial ℤ) (P β : ℝ) :
    integerPolynomialWeyl f P ((a:ℝ)/q+β) =
      rationalPolynomialWeightedSum q (C a*f) (ordinaryNumbers P)
        (fun n => e (β*(f.map (Int.castRingHom ℝ)).eval (n:ℝ))) := by
  unfold integerPolynomialWeyl rationalPolynomialWeightedSum
  apply Finset.sum_congr rfl
  intro n _
  have hchar : ZMod.stdAddChar ((a*f.eval (n:ℤ):ℤ):ZMod q)=
      e (((a*f.eval (n:ℤ):ℤ):ℝ)/q) := by
    simpa only [pow_zero, mul_one] using stdAddChar_monomial_nat q 0 (a*f.eval (n:ℤ)) 1
  simp only [Polynomial.eval_natCast_map, Polynomial.eval_mul, Polynomial.eval_C]
  change e (((a:ℝ)/q+β)*((f.eval (n:ℤ):ℤ):ℝ)) =
    ZMod.stdAddChar ((a*f.eval (n:ℤ):ℤ):ZMod q)*e (β*((f.eval (n:ℤ):ℤ):ℝ))
  rw [hchar, ← e_add]
  congr 1
  push_cast
  ring

theorem source_broad_major_approximation (k j : ℕ) (hj : j+2≤k)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ)
      (params : List (ℤ × ℤ)) (P β : ℝ),
      params.length=j → (∀ hm ∈ params, 0<hm.1 ∧ 0<hm.2) → 0≤P →
      |β| *((powerPolynomial k params).map (Int.castRingHom ℝ)).derivative.eval P≤1/(2*(q:ℝ)) →
      ‖integerPolynomialWeyl (powerPolynomial k params) P ((a:ℝ)/q+β)-
        (integerPolynomialSum q (C a*powerPolynomial k params)/(q:ℂ))*
          polynomialIntegral ((powerPolynomial k params).map (Int.castRingHom ℝ)) P β‖ ≤
        C₀*(q:ℝ)^(1-1/((k-j:ℕ):ℝ)+ε) := by
  have hD : 2≤k-j := by omega
  have hK : 1≤leadingMultiplier k j := by
    unfold leadingMultiplier
    exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.descFactorial_pos.mpr (by omega))
  obtain ⟨C₀,hC₀,hbroad⟩ := polynomial_broad_major_approximation (k-j) (leadingMultiplier k j) hD hK hε
  refine ⟨C₀,hC₀,?_⟩
  intro q _ a params P β hlen hparams hP hβ
  have hnonzero : ∀ hm ∈ params, hm.1≠0 ∧ hm.2≠0 :=
    fun hm hhm => ⟨(hparams hm hhm).1.ne', (hparams hm hhm).2.ne'⟩
  have hlenk : params.length≤k := by omega
  obtain ⟨L,hL⟩ := powerPolynomial_coefficient_relation k params hnonzero hlenk 1
  rw [hlen] at hL
  have hrel : (leadingMultiplier k j:ℤ)*(C a*powerPolynomial k params).coeff 1 =
      (C a*powerPolynomial k params).coeff (k-j)*L := by
    simp only [Polynomial.coeff_C_mul]
    linear_combination a*hL
  have hdeg : (C a*powerPolynomial k params).natDegree≤k-j :=
    (Polynomial.natDegree_C_mul_le a _).trans (by
      rw [powerPolynomial_natDegree k params hnonzero hlenk, hlen])
  have hpos := powerPolynomial_real_nonnegative k params
    (fun hm hhm => ⟨(hparams hm hhm).1.le, (hparams hm hhm).2⟩)
  rw [integerPolynomialWeyl_rational]
  exact hbroad q (C a*powerPolynomial k params) _ L P β hdeg hrel hpos hP hβ

theorem integerPolynomialWeyl_eq_source_sum (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2≠0) (P α : ℝ) :
    integerPolynomialWeyl (powerPolynomial k params) P α =
      ∑ n ∈ ordinaryNumbers P, e (α*Differences.modifiedCenteredPower k (realParameters params) (n:ℝ)) := by
  unfold integerPolynomialWeyl
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.eval_map, powerPolynomial_eval_real k params hm]

#print axioms source_broad_major_approximation
#print axioms integerPolynomialWeyl_eq_source_sum
end Waring.PolicyCompletionSourceMajor
