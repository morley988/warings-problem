import Waring.SeedCompletionSharpBackward
import Waring.Holder

/-!
# Terminal Holder for the sharp first-difference cross integral

The second- and fourth-moment versions are inequalities for the actual
finite exponential sums. The factors at scaled frequencies have exactly
the ordinary smooth moments by integer-frequency orthogonality.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace Waring.SeedCompletionTerminalHolder
open SeedCompletionSharpBackward SeedCompletionBackwardAggregate
open PolicyCompletionHolder PolicyCompletionGoodBranch SmoothMoments

/-- A two-factor Holder inequality with explicit natural powers. -/
theorem interval_product_powers_holder {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (p q m n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : (p : ℝ) = (m : ℝ)*t) (hq : (q : ℝ) = (n : ℝ)*(1-t)) :
    (∫ x in (0 : ℝ)..1, F x^p * G x^q) ≤
      (∫ x in (0 : ℝ)..1, F x^m)^t *
      (∫ x in (0 : ℝ)..1, G x^n)^(1-t) := by
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hfm : Integrable (fun x => F x^m) μ := (hF.pow m).integrableOn_Ioc
  have hgn : Integrable (fun x => G x^n) μ := (hG.pow n).integrableOn_Ioc
  have hprod : Integrable (fun x => F x^p * G x^q) μ :=
    ((hF.pow p).mul (hG.pow q)).integrableOn_Ioc
  have H := ENNReal.lintegral_mul_norm_pow_le
    hfm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hgn.aestronglyMeasurable.aemeasurable.ennreal_ofReal ht0 ht' (by ring : t+(1-t)=1)
  have heq (x : ℝ) :
      ENNReal.ofReal (F x^m)^t * ENNReal.ofReal (G x^n)^(1-t) =
      ENNReal.ofReal (F x^p * G x^q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hF0 x) _) ht0,
      ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hG0 x) _) ht',
      ← Real.rpow_natCast_mul (hF0 x),← Real.rpow_natCast_mul (hG0 x),
      ← hp,← hq,Real.rpow_natCast,Real.rpow_natCast,
      ← ENNReal.ofReal_mul (pow_nonneg (hF0 x) _)]
  simp_rw [heq] at H
  have hfn : 0 ≤ᵐ[μ] (fun x => F x^m) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (hF0 x) _)
  have hgnn : 0 ≤ᵐ[μ] (fun x => G x^n) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (hG0 x) _)
  have hpn : 0 ≤ᵐ[μ] (fun x => F x^p*G x^q) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg
      (pow_nonneg (hF0 x) _) (pow_nonneg (hG0 x) _))
  rw [← ofReal_integral_eq_lintegral_ofReal hprod hpn,
    ← ofReal_integral_eq_lintegral_ofReal hfm hfn,
    ← ofReal_integral_eq_lintegral_ofReal hgn hgnn] at H
  have hiF := integral_nonneg_of_ae hfn
  have hiG := integral_nonneg_of_ae hgnn
  rw [ENNReal.ofReal_rpow_of_nonneg hiF ht0,
    ENNReal.ofReal_rpow_of_nonneg hiG ht',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hiF _)] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (Real.rpow_nonneg hiF _) (Real.rpow_nonneg hiG _))).mp H

/-- Multiplying every frequency by a nonzero integer preserves every even
moment, through exact cancellation in the equal-sum equation. -/
theorem frequencyEvenMoment_mul_frequency {ι : Type*} (A : Finset ι)
    (f : ι → ℤ) (s : ℕ) (c : ℤ) (hc : c ≠ 0) :
    frequencyEvenMoment A (fun a => c*f a) s = frequencyEvenMoment A f s := by
  classical
  rw [frequencyEvenMoment_eq_card,frequencyEvenMoment_eq_card]
  have heq : equalSumPairs A (fun a => c*f a) s = equalSumPairs A f s := by
    ext p
    simp only [equalSumPairs,Finset.mem_filter,Finset.mem_product,← Finset.mul_sum,
      mul_right_inj' hc]
  rw [heq]

/-- The actual scaled tuple sum is the corresponding smooth sum power. -/
theorem frequencySum_scaled_smoothTuple (k s : ℕ) (Q R : ℝ) (c : ℤ) (x : ℝ) :
    frequencySum (finiteTuples (smoothNumbers Q R) s)
      (fun u => c*smoothTupleValue k s u) x =
      (frequencySum (smoothNumbers Q R) (fun n => c*((n^k : ℕ) : ℤ)) x)^s := by
  unfold frequencySum
  rw [sum_pow_fourier]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  simp [smoothTupleValue,Finset.mul_sum]

/-- The next smooth cross integral retains exactly 2s smooth powers. -/
theorem nextSmoothCrossIntegral_eq {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    nextSmoothCrossIntegral k s C params W N Q R =
      ∫ x in (0 : ℝ)..1,
        ‖frequencySum (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
          (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ))) x‖ *
        ‖frequencySum (smoothNumbers Q R) (fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)) x‖^(2*s) := by
  unfold nextSmoothCrossIntegral aggregateNextCrossIntegral
  congr 1
  funext x
  rw [frequencySum_scaled_smoothTuple,norm_pow,← pow_mul,Nat.mul_comm s 2]

/-- The B terminal at its second-moment endpoint, for every smooth order. -/
theorem nextSmoothCrossIntegral_le_second {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    nextSmoothCrossIntegral k s C params W N Q R ≤
      (frequencyEvenMoment (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
        (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ))) 1)^(1/2 : ℝ) *
      (smoothMoment k (4*s) Q R)^(1/2 : ℝ) := by
  let A := aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k
  let f := aggregateNextPhase k (fun p : κ × ℕ => params p.1) (fun p => (p.2 : ℤ))
  let B := smoothNumbers Q R
  let g := fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)
  have H := interval_product_powers_holder (continuous_frequencySum A f).norm
    (continuous_frequencySum B g).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    1 (2*s) 2 (4*s) (t := 1/2) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring)
  rw [nextSmoothCrossIntegral_eq]
  have heq : (∫ x in (0 : ℝ)..1, ‖frequencySum B g x‖^(4*s)) =
      smoothMoment k (4*s) Q R := by
    rw [show 4*s=2*(2*s) by omega]
    change frequencyEvenMoment B g (2*s) = _
    rw [frequencyEvenMoment_mul_frequency B (fun n => ((n^k : ℕ) : ℤ))
      (2*s) ((2 : ℤ)^k) (by positivity)]
    exact (smoothMoment_even_eq_frequency k (2*s) Q R).symm
  norm_num only [pow_one,show (1 : ℝ)-(1/2)=1/2 by norm_num] at H
  rw [heq] at H
  exact H

/-- The A_1^(4,2) terminal: one fourth auxiliary moment and the eighth
smooth moment, with exact Holder weights 1/4 and 3/4. -/
theorem nextSmoothCrossIntegral_le_fourth {κ : Type*} (k : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    nextSmoothCrossIntegral k 3 C params W N Q R ≤
      (frequencyEvenMoment (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
        (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ))) 2)^(1/4 : ℝ) *
      (smoothMoment k 8 Q R)^(3/4 : ℝ) := by
  let A := aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k
  let f := aggregateNextPhase k (fun p : κ × ℕ => params p.1) (fun p => (p.2 : ℤ))
  let B := smoothNumbers Q R
  let g := fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)
  have H := interval_product_powers_holder (continuous_frequencySum A f).norm
    (continuous_frequencySum B g).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    1 6 4 8 (t := 1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [nextSmoothCrossIntegral_eq]
  have heq : (∫ x in (0 : ℝ)..1, ‖frequencySum B g x‖^8) =
      smoothMoment k 8 Q R := by
    change frequencyEvenMoment B g 4 = _
    rw [frequencyEvenMoment_mul_frequency B (fun n => ((n^k : ℕ) : ℤ))
      4 ((2 : ℤ)^k) (by positivity)]
    exact (smoothMoment_even_eq_frequency k 4 Q R).symm
  norm_num only [pow_one,show (1 : ℝ)-(1/4)=3/4 by norm_num] at H
  rw [heq] at H
  exact H

#print axioms nextSmoothCrossIntegral_le_second
#print axioms nextSmoothCrossIntegral_le_fourth
end Waring.SeedCompletionTerminalHolder
