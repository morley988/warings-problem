import Waring.SeedCompletionEvenSecondScales
import Waring.SeedCompletionSecondHolder

/-! # Actual even second-stage Holder bounds for the seed recurrence -/

noncomputable section
namespace Waring.SeedCompletionSecondScales
open SmoothMoments SeedCompletionSourceBounds SeedCompletionSecondTransport
open PolicyCompletionHolder SeedCompletionInitialMixed SeedCompletionBackwardAggregate
open SeedCompletionSharpBackward CoefficientPower SeedCompletionTerminalThree FirstDifferenceSecond

theorem even_A_second_cross (d : ℕ) (hd : supportedHalfDegree d) {u v w : ℕ} {φ₁ φ₂ a b c lamv lamw : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/((2*d : ℕ) : ℝ)) (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/((2*d : ℕ) : ℝ))
    (hv : AdmissibleExponent (2*d) (2*v) lamv) (hw : AdmissibleExponent (2*d) (2*w) lamw)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 4*a=1) (hsmooth : (v : ℝ)*b+(w : ℝ)*c=(u : ℝ)) :
    SourcePowerBound (secondCross (2*d) u φ₁ φ₂)
      ((8-3*(2*(d : ℝ)-1)*(φ₁+φ₂))*a+((1-φ₁-φ₂)*lamv)*b+((1-φ₁-φ₂)*lamw)*c) := by
  have hφ₁eight := hφ₁k.trans (even_half_reciprocal_le d hd)
  have hφ₂eight := hφ₂k.trans (even_half_reciprocal_le d hd)
  have hq0 : 0 ≤ 1-φ₁-φ₂ := by linarith
  have hq1 : 1-φ₁-φ₂ ≤ 1 := by linarith
  have hF := (even_fourth_power d hd hφ₁ hφ₁k hφ₂ hφ₂k).rpow ha
    (fun P R _ _ => secondMoment_nonneg ..)
  have hV := (admissible_shorter_source_bound hv (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1).rpow hb
    (fun P R _ _ => smoothMoment_nonneg ..)
  have hW := (admissible_shorter_source_bound hw (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1).rpow hc
    (fun P R _ _ => smoothMoment_nonneg ..)
  apply ((hF.mul hV).mul hW).of_le
    (fun P R _ _ => secondCross_nonneg ..)
  intro P R hP hR
  exact secondCross_le_A (2*d) u 2 v w hP hφ₁ ha hb hc hsum (by norm_num; exact haux) hsmooth

theorem even_B_second_cross (d : ℕ) (hd : supportedHalfDegree d) {u t : ℕ} {φ₁ φ₂ a b c lam : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/((2*d : ℕ) : ℝ)) (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/((2*d : ℕ) : ℝ))
    (ht : AdmissibleExponent (2*d) (2*t) lam)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 2*a+4*b=1) (hsmooth : (t : ℝ)*c=(u : ℝ)) :
    SourcePowerBound (secondCross (2*d) u φ₁ φ₂)
      ((3-(2*(d : ℝ)-1)*(φ₁+φ₂))*a+(8-3*(2*(d : ℝ)-1)*(φ₁+φ₂))*b+((1-φ₁-φ₂)*lam)*c) := by
  have hφ₁eight := hφ₁k.trans (even_half_reciprocal_le d hd)
  have hφ₂eight := hφ₂k.trans (even_half_reciprocal_le d hd)
  have hq0 : 0 ≤ 1-φ₁-φ₂ := by linarith
  have hq1 : 1-φ₁-φ₂ ≤ 1 := by linarith
  have hF := (even_second_power d hd hφ₁ hφ₁k hφ₂ hφ₂k).rpow ha
    (fun P R _ _ => secondMoment_nonneg ..)
  have hG := (even_fourth_power d hd hφ₁ hφ₁k hφ₂ hφ₂k).rpow hb
    (fun P R _ _ => secondMoment_nonneg ..)
  have hU := (admissible_shorter_source_bound ht (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1).rpow hc
    (fun P R _ _ => smoothMoment_nonneg ..)
  apply ((hF.mul hG).mul hU).of_le
    (fun P R _ _ => secondCross_nonneg ..)
  intro P R hP hR
  exact secondCross_le_B (2*d) u 1 2 t hP hφ₁ ha hb hc hsum (by norm_num; exact haux) hsmooth

#print axioms even_A_second_cross
#print axioms even_B_second_cross
end Waring.SeedCompletionSecondScales
