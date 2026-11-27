import Waring.SeedCompletionTerminalHolder

/-!
# The exact three-factor Holder terminals for the source A and B processes

The two powers of the repeated factor may be different. This permits
interpolating adjacent smooth moments in A and adjacent auxiliary moments
in B, with the literal nonnegative weights checked by real equalities.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace Waring.SeedCompletionTerminalThree
open SeedCompletionTerminalHolder SeedCompletionSharpBackward
open SeedCompletionBackwardAggregate PolicyCompletionHolder SmoothMoments

theorem interval_three_powers_holder {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x,0 ≤ F x) (hG0 : ∀ x,0 ≤ G x)
    (p q m n l : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (hp : (p : ℝ)=(m : ℝ)*a) (hq : (q : ℝ)=(n : ℝ)*b+(l : ℝ)*c) :
    (∫ x in (0 : ℝ)..1,F x^p*G x^q) ≤
      (∫ x in (0 : ℝ)..1,F x^m)^a*
        (∫ x in (0 : ℝ)..1,G x^n)^b*(∫ x in (0 : ℝ)..1,G x^l)^c := by
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hfm : Integrable (fun x => F x^m) μ := (hF.pow m).integrableOn_Ioc
  have hgn : Integrable (fun x => G x^n) μ := (hG.pow n).integrableOn_Ioc
  have hgl : Integrable (fun x => G x^l) μ := (hG.pow l).integrableOn_Ioc
  have hpq : Integrable (fun x => F x^p*G x^q) μ := ((hF.pow p).mul (hG.pow q)).integrableOn_Ioc
  have H := Holder.mixed (μ := μ) hF.measurable.aemeasurable.ennreal_ofReal
    hG.measurable.aemeasurable.ennreal_ofReal (m := (m : ℝ)) (n := (n : ℝ)) (p := (l : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha hb hc hsum
  rw [← hp,← hq] at H
  have hfp (x : ℝ) (r : ℕ) : ENNReal.ofReal (F x)^(r : ℝ)=ENNReal.ofReal (F x^r) := by
    rw [ENNReal.rpow_natCast,ENNReal.ofReal_pow (hF0 x)]
  have hgp (x : ℝ) (r : ℕ) : ENNReal.ofReal (G x)^(r : ℝ)=ENNReal.ofReal (G x^r) := by
    rw [ENNReal.rpow_natCast,ENNReal.ofReal_pow (hG0 x)]
  simp_rw [hfp,hgp,← ENNReal.ofReal_mul (pow_nonneg (hF0 _) p)] at H
  have hfn (r : ℕ) : 0 ≤ᵐ[μ] (fun x => F x^r) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (hF0 x) _)
  have hgnn (r : ℕ) : 0 ≤ᵐ[μ] (fun x => G x^r) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (hG0 x) _)
  have hpqn : 0 ≤ᵐ[μ] (fun x => F x^p*G x^q) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (hF0 x) _) (pow_nonneg (hG0 x) _))
  rw [← ofReal_integral_eq_lintegral_ofReal hpq hpqn,
    ← ofReal_integral_eq_lintegral_ofReal hfm (hfn m),
    ← ofReal_integral_eq_lintegral_ofReal hgn (hgnn n),
    ← ofReal_integral_eq_lintegral_ofReal hgl (hgnn l)] at H
  have hiF := integral_nonneg_of_ae (hfn m)
  have hiG := integral_nonneg_of_ae (hgnn n)
  have hiG' := integral_nonneg_of_ae (hgnn l)
  rw [ENNReal.ofReal_rpow_of_nonneg hiF ha,ENNReal.ofReal_rpow_of_nonneg hiG hb,
    ENNReal.ofReal_rpow_of_nonneg hiG' hc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hiF _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hiF _) (Real.rpow_nonneg hiG _))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hiF _) (Real.rpow_nonneg hiG _))
    (Real.rpow_nonneg hiG' _))).mp H

theorem scaled_smooth_even_integral (k t : ℕ) (Q R : ℝ) :
    (∫ x in (0 : ℝ)..1,
      ‖frequencySum (smoothNumbers Q R) (fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)) x‖^(2*t)) =
      smoothMoment k (2*t) Q R := by
  change frequencyEvenMoment _ _ t = _
  rw [frequencyEvenMoment_mul_frequency _ _ t ((2 : ℤ)^k) (by positivity),
    ← smoothMoment_even_eq_frequency]

/-- One auxiliary moment and two independently available smooth moments. -/
theorem nextSmoothCrossIntegral_le_A {κ : Type*} (k s r v w : ℕ)
    (C : Finset κ) (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : (2*(r : ℝ))*a=1) (hsmooth : (v : ℝ)*b+(w : ℝ)*c=(s : ℝ)) :
    nextSmoothCrossIntegral k s C params W N Q R ≤
      (frequencyEvenMoment (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
        (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ))) r)^a*
      (smoothMoment k (2*v) Q R)^b*(smoothMoment k (2*w) Q R)^c := by
  let A := aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k
  let f := aggregateNextPhase k (fun p : κ × ℕ => params p.1) (fun p => (p.2 : ℤ))
  let B := smoothNumbers Q R
  let g := fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)
  have H := interval_three_powers_holder (continuous_frequencySum A f).norm
    (continuous_frequencySum B g).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    1 (2*s) (2*r) (2*v) (2*w) ha hb hc hsum
    (by push_cast; linarith) (by push_cast; linarith)
  rw [nextSmoothCrossIntegral_eq]
  simp only [pow_one] at H
  rw [scaled_smooth_even_integral k v Q R,scaled_smooth_even_integral k w Q R] at H
  exact H

/-- Two auxiliary moments and one smooth moment, retaining the precise
source B-process weights. -/
theorem nextSmoothCrossIntegral_le_B {κ : Type*} (k s r v t : ℕ)
    (C : Finset κ) (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : (2*(r : ℝ))*a+(2*(v : ℝ))*b=1) (hsmooth : (t : ℝ)*c=(s : ℝ)) :
    nextSmoothCrossIntegral k s C params W N Q R ≤
      (frequencyEvenMoment (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
        (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ))) r)^a*
      (frequencyEvenMoment (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
        (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ))) v)^b*
      (smoothMoment k (2*t) Q R)^c := by
  let A := aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k
  let f := aggregateNextPhase k (fun p : κ × ℕ => params p.1) (fun p => (p.2 : ℤ))
  let B := smoothNumbers Q R
  let g := fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)
  have H := interval_three_powers_holder (continuous_frequencySum B g).norm
    (continuous_frequencySum A f).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (2*s) 1 (2*t) (2*r) (2*v) hc ha hb (by linarith)
    (by push_cast; linarith) (by push_cast; linarith)
  rw [scaled_smooth_even_integral k t Q R] at H
  rw [nextSmoothCrossIntegral_eq]
  simp only [pow_one] at H
  simpa only [A,B,f,g,frequencyEvenMoment,frequencySum,mul_comm,mul_left_comm,mul_assoc] using H

#print axioms interval_three_powers_holder
#print axioms nextSmoothCrossIntegral_le_A
#print axioms nextSmoothCrossIntegral_le_B
end Waring.SeedCompletionTerminalThree
