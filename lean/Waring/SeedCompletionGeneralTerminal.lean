import Waring.SeedCompletionPaddedHigherPower
import Waring.SeedCompletionTerminalThree

/-! # Exact A/B Holder terminals for arbitrary full source depth -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionGeneralTerminal
open SeedCompletionPaddedSource SeedCompletionWeylTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionTerminalThree
open PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges PolicyCompletionHolder SmoothMoments

theorem paddedMoment_zero_eq {j : ℕ} (k s : ℕ) (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) :
    paddedMoment k 0 s D φ P R=
      ∫ α in (0:ℝ)..1,‖boxSourceFamily k (D*P) P R (fun i=>P^(φ i)) α‖^(2*s) := by
  have hH : paddedHeights k 0 (D*P) (fun i=>P^(φ i))=
      originalHeights k (D*P) (fun i=>P^(φ i)) := by
    unfold paddedHeights
    rw [Fin.append_right_nil _ _ rfl]
    rfl
  have hA : paddedCoefficients 0 P R (fun i=>P^(φ i))=
      originalCoefficients P R (fun i=>P^(φ i)) := by
    unfold paddedCoefficients
    rw [Fin.append_right_nil _ _ rfl]
    rfl
  unfold paddedMoment
  rw [hH,hA]
  simp only [sourceMoment,frequencyEvenMoment,sourceDomain,sourceLabels,
    originalHeights,originalCoefficients,rangeSet,naturalBoxDomain,naturalBoxLabels,
    CartesianProductSampling.positiveBox,boxHeightBounds,boxCoefficientTuples,
    boxSourceFamily_eq_frequency,frequencySum,ordinaryNumbers]
  rfl

theorem full_cross_le_A {j : ℕ} (k s r v w : ℕ) (D : ℝ) (φ : Fin j→ℝ)
    (P R : ℝ) {a b c : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hsum : a+b+c=1)
    (haux : (2*(r:ℝ))*a=1) (hsmooth : (v:ℝ)*b+(w:ℝ)*c=(s:ℝ)) :
    powerBoxCross k s D φ P R≤(paddedMoment k 0 r D φ P R)^a*
      (smoothMoment k (2*v) (D*P^(1-total φ)) R)^b*
      (smoothMoment k (2*w) (D*P^(1-total φ)) R)^c := by
  have hF : Continuous (boxSourceFamily k (D*P) P R (fun i=>P^(φ i))) := by
    have heq : boxSourceFamily k (D*P) P R (fun i=>P^(φ i)) =
        frequencySum (naturalBoxDomain k (D*P) P R (fun i=>P^(φ i))) (naturalPhase k) := by
      funext α
      exact boxSourceFamily_eq_frequency k (D*P) P R (fun i=>P^(φ i)) α
    rw [heq]
    exact continuous_frequencySum _ _
  have H := interval_three_powers_holder hF.norm
    (continuous_smoothWeyl k (D*P^(1-total φ)) R).norm
    (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
    1 (2*s) (2*r) (2*v) (2*w) ha hb hc hsum
    (by push_cast; linarith) (by push_cast; linarith)
  rw [paddedMoment_zero_eq]
  simpa only [powerBoxCross,boxCrossMoment,smoothMoment,pow_one] using H

theorem full_cross_le_B {j : ℕ} (k s r v t : ℕ) (D : ℝ) (φ : Fin j→ℝ)
    (P R : ℝ) {a b c : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hsum : a+b+c=1)
    (haux : (2*(r:ℝ))*a+(2*(v:ℝ))*b=1) (hsmooth : (t:ℝ)*c=(s:ℝ)) :
    powerBoxCross k s D φ P R≤(paddedMoment k 0 r D φ P R)^a*
      (paddedMoment k 0 v D φ P R)^b*
      (smoothMoment k (2*t) (D*P^(1-total φ)) R)^c := by
  have hF : Continuous (boxSourceFamily k (D*P) P R (fun i=>P^(φ i))) := by
    have heq : boxSourceFamily k (D*P) P R (fun i=>P^(φ i)) =
        frequencySum (naturalBoxDomain k (D*P) P R (fun i=>P^(φ i))) (naturalPhase k) := by
      funext α
      exact boxSourceFamily_eq_frequency k (D*P) P R (fun i=>P^(φ i)) α
    rw [heq]
    exact continuous_frequencySum _ _
  have H := interval_three_powers_holder
    (continuous_smoothWeyl k (D*P^(1-total φ)) R).norm hF.norm
    (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
    (2*s) 1 (2*t) (2*r) (2*v) hc ha hb (by linarith)
    (by push_cast; linarith) (by push_cast; linarith)
  rw [paddedMoment_zero_eq,paddedMoment_zero_eq]
  simpa only [powerBoxCross,boxCrossMoment,smoothMoment,pow_one,
    mul_comm,mul_left_comm,mul_assoc] using H

theorem full_A_cross_power {k j s r v w : ℕ} {D a b c κ lamv lamw : ℝ}
    (hD : 1≤D) (φ : Fin j→ℝ) (hq0 : 0≤1-total φ) (hq1 : 1-total φ≤1)
    (hauxiliary : SourcePowerBound (paddedMoment k 0 r D φ) κ)
    (hv : AdmissibleExponent k (2*v) lamv) (hw : AdmissibleExponent k (2*w) lamw)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hsum : a+b+c=1)
    (haux : (2*(r:ℝ))*a=1) (hsmooth : (v:ℝ)*b+(w:ℝ)*c=(s:ℝ)) :
    SourcePowerBound (powerBoxCross k s D φ)
      (κ*a+((1-total φ)*lamv)*b+((1-total φ)*lamw)*c) := by
  have hF := hauxiliary.rpow ha (fun P R _ _=>paddedMoment_nonneg ..)
  have hV := (admissible_shorter_source_bound hv hD hq0 hq1).rpow hb
    (fun P R _ _=>smoothMoment_nonneg ..)
  have hW := (admissible_shorter_source_bound hw hD hq0 hq1).rpow hc
    (fun P R _ _=>smoothMoment_nonneg ..)
  apply ((hF.mul hV).mul hW).of_le (fun P R _ _=>boxCrossMoment_nonneg ..)
  intro P R hP hR
  exact full_cross_le_A k s r v w D φ P R ha hb hc hsum haux hsmooth

theorem full_B_cross_power {k j s r v t : ℕ} {D a b c κr κv lamt : ℝ}
    (hD : 1≤D) (φ : Fin j→ℝ) (hq0 : 0≤1-total φ) (hq1 : 1-total φ≤1)
    (hr : SourcePowerBound (paddedMoment k 0 r D φ) κr)
    (hv : SourcePowerBound (paddedMoment k 0 v D φ) κv)
    (ht : AdmissibleExponent k (2*t) lamt)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hsum : a+b+c=1)
    (haux : (2*(r:ℝ))*a+(2*(v:ℝ))*b=1) (hsmooth : (t:ℝ)*c=(s:ℝ)) :
    SourcePowerBound (powerBoxCross k s D φ)
      (κr*a+κv*b+((1-total φ)*lamt)*c) := by
  have hF := hr.rpow ha (fun P R _ _=>paddedMoment_nonneg ..)
  have hG := hv.rpow hb (fun P R _ _=>paddedMoment_nonneg ..)
  have hT := (admissible_shorter_source_bound ht hD hq0 hq1).rpow hc
    (fun P R _ _=>smoothMoment_nonneg ..)
  apply ((hF.mul hG).mul hT).of_le (fun P R _ _=>boxCrossMoment_nonneg ..)
  intro P R hP hR
  exact full_cross_le_B k s r v t D φ P R ha hb hc hsum haux hsmooth

#print axioms full_A_cross_power
#print axioms full_B_cross_power
end Waring.SeedCompletionGeneralTerminal
