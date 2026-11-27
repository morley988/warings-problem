import Waring.PolicyCompletionBackward
import Waring.SeedCompletionBackwardAggregate

/-!
# The actual all-good forward/backward recurrence

This module composes the completed all-good factor extraction and root
conditioning with the complete backward-differencing moment. All old
parameters and extracted coefficients are kept inside one next-stage
auxiliary square, so the Cauchy step introduces no extra parameter count.
The ordinary factor is the actual even smooth moment, by orthogonality.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionGoodRecurrence
open PolicyCompletionGoodBranch PolicyCompletionBackward
open SeedCompletionBackward SeedCompletionBackwardMoments SeedCompletionBackwardAggregate
open IntegerDifferencePolynomial SmoothMoments

/-- A complete second moment of the smooth tuple sum is its ordinary even
moment, with all ordered tuples preserved. -/
theorem tuple_secondMoment_eq_evenMoment (k s : ℕ) (B : Finset ℕ) :
    secondMoment (finiteTuples B s) (smoothTupleValue k s) =
      frequencyEvenMoment B (fun n => ((n^k : ℕ) : ℤ)) s := by
  rw [secondMoment_eq_count,frequencyEvenMoment_eq_card]
  apply congrArg (fun T : Finset ((Fin s → ℕ) × (Fin s → ℕ)) => (T.card : ℝ))
  ext p
  simp only [SeedCompletionBackwardCount.crossFrequencyPairs,equalSumPairs,
    Finset.mem_filter,Finset.mem_product,smoothTupleValue,Nat.cast_pow]

theorem tuple_secondMoment_eq_smoothMoment (k s : ℕ) (Q R : ℝ) :
    secondMoment (finiteTuples (smoothNumbers Q R) s) (smoothTupleValue k s) =
      smoothMoment k (2*s) Q R := by
  rw [tuple_secondMoment_eq_evenMoment,smoothMoment_even_eq_frequency]

/-- The full next auxiliary moment, retaining the old parameter and the
new smooth block divisor together inside its square. -/
def nextSmoothMoment {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) : ℝ :=
  aggregateNextMoment k (C ×ˢ W) (fun p => params p.1) (fun p => (p.2 : ℤ)) N
    (finiteTuples (smoothNumbers Q R) s) (smoothTupleValue k s)

/-- The actual sum of common-modulus counts satisfies the source backward
step, with one complete auxiliary moment and the actual smooth moment. -/
theorem commonModulus_sum_le_nextMoment {κ : Type*} [DecidableEq κ]
    (k s : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ))
    (W : Finset ℕ) (N : ℤ) (Z : Finset ℤ) (Q R : ℝ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0)
    (hw : ∀ w ∈ W, 0 < w) (hZ : Z ⊆ Finset.Icc 1 N) :
    (∑ w ∈ W,
      ((commonModulusSolutions (C ×ˢ Z) (smoothNumbers Q R)
        (fun c => powerPolynomial k (params c)) s k w).card : ℝ)) ≤
      (C.card : ℝ)*(W.card : ℝ)*(Z.card : ℝ)*smoothMoment k (2*s) Q R +
        2*Real.sqrt (nextSmoothMoment k s C params W N Q R * smoothMoment k (2*s) Q R) := by
  classical
  have hcount : (∑ w ∈ W,
      ((commonModulusSolutions (C ×ˢ Z) (smoothNumbers Q R)
        (fun c => powerPolynomial k (params c)) s k w).card : ℝ)) =
      ∑ p ∈ C ×ˢ W,
        ((stepSolutions k (realParameters (params p.1)) (p.2 : ℤ) Z
          (finiteTuples (smoothNumbers Q R) s) (fun u => (smoothTupleValue k s u : ℝ))).card : ℝ) := by
    rw [Finset.sum_product,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    exact_mod_cast commonModulus_card_eq_sum_steps C Z (smoothNumbers Q R) params k s w hm
  rw [hcount]
  have H := sum_backward_count_le_moments k (C ×ˢ W) (fun p => params p.1)
    (fun p => (p.2 : ℤ)) N (fun _ => Z) (finiteTuples (smoothNumbers Q R) s)
    (smoothTupleValue k s)
    (fun p hp => hm p.1 (Finset.mem_product.mp hp).1)
    (fun p hp => by
      change (0 : ℤ) < (p.2 : ℤ)
      exact_mod_cast hw p.2 (Finset.mem_product.mp hp).2)
    (fun _ _ => hZ)
  rw [tuple_secondMoment_eq_smoothMoment] at H
  simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_product,Nat.cast_mul,mul_assoc,
    nextSmoothMoment] using H

theorem nextSmoothMoment_nonneg {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    0 ≤ nextSmoothMoment k s C params W N Q R :=
  secondMoment_nonneg _ _

/-- A complete, uniform recurrence for the actual all-good part of the
smooth mixed moment. Every source ingredient in this branch is proved. -/
theorem goodSmooth_count_le_nextMoment {κ : Type*} [DecidableEq κ]
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C : Finset κ) (params : κ → List (ℤ × ℤ)),
      (∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) →
      ∀ s : ℕ, 0 < s → ∀ (N : ℤ) (Z : Finset ℤ), Z ⊆ Finset.Icc 1 N →
      ∀ Q R M : ℝ, 1 ≤ Q → 1 ≤ M →
      ((goodSmoothSolutions (C ×ˢ Z) (fun c => powerPolynomial k (params c)) s k Q R M).card : ℝ) ≤
        K*(C.card : ℝ)*Q^ε*((CoefficientPower.coefficientBlock Q R M).card : ℝ)^(2*s-1) *
          ((C.card : ℝ)*((CoefficientPower.coefficientBlock Q R M).card : ℝ)*(Z.card : ℝ)*
              smoothMoment k (2*s) (Q/M) R +
            2*Real.sqrt (nextSmoothMoment k s C params (CoefficientPower.coefficientBlock Q R M)
              N (Q/M) R * smoothMoment k (2*s) (Q/M) R)) := by
  obtain ⟨K,hK,hgood⟩ := goodSmooth_count_le_common_modulus (κ := κ) k k hε
  refine ⟨K,hK,?_⟩
  intro C params hm s hs N Z hZ Q R M hQ hM
  let W := CoefficientPower.coefficientBlock Q R M
  let J := smoothMoment k (2*s) (Q/M) R
  let T := (C.card : ℝ)*(W.card : ℝ)*(Z.card : ℝ)*J +
    2*Real.sqrt (nextSmoothMoment k s C params W N (Q/M) R * J)
  have hdegree : ∀ c ∈ (C ×ˢ Z).image Prod.fst,
      (powerPolynomial k (params c)).natDegree ≤ k := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact (powerPolynomial_natDegree_le k (params x.1)
      (hm x.1 (Finset.mem_product.mp hx).1)).trans (Nat.sub_le _ _)
  have HG := hgood (C ×ˢ Z) (fun c => powerPolynomial k (params c)) hdegree s hs Q R M hQ hM
  have hWpos : ∀ w ∈ W, 0 < w := by
    intro w hw
    exact (mem_smoothNumbers.mp (Finset.mem_filter.mp hw).1).1.1
  have HT := commonModulus_sum_le_nextMoment k s C params W N Z (Q/M) R hm hWpos hZ
  have hparams : (((C ×ˢ Z).image Prod.fst).card : ℝ) ≤ (C.card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_product.mp hx).1
  have hT0 : 0 ≤ T := by
    have hJ : 0 ≤ J := smoothMoment_nonneg _ _ _ _
    dsimp only [T]
    positivity
  have hcoef : K*(((C ×ˢ Z).image Prod.fst).card : ℝ)*Q^ε*(W.card : ℝ)^(2*s-1) ≤
      K*(C.card : ℝ)*Q^ε*(W.card : ℝ)^(2*s-1) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hparams hK.le)
        (Real.rpow_nonneg (zero_le_one.trans hQ) ε)) (by positivity)
  apply HG.trans
  apply (mul_le_mul_of_nonneg_left HT (by positivity)).trans
  exact mul_le_mul_of_nonneg_right hcoef hT0

#print axioms commonModulus_sum_le_nextMoment
#print axioms goodSmooth_count_le_nextMoment

end Waring.PolicyCompletionGoodRecurrence
