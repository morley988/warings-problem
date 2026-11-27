import Waring.SeedCompletionSecondScales
import Waring.SeedCompletionTerminalThree

/-! # Actual second-stage Holder terminals at fixed power scales -/
noncomputable section
namespace Waring.SeedCompletionSecondScales
open SmoothMoments SeedCompletionSourceBounds SeedCompletionSecondTransport
open PolicyCompletionHolder SeedCompletionInitialMixed SeedCompletionBackwardAggregate
open SeedCompletionSharpBackward CoefficientPower SeedCompletionTerminalThree

theorem first_next_moment_le_second_scale (k r : ℕ) {φ₁ φ₂ P R : ℝ}
    (hP : 1 ≤ P) (hφ₁ : 0 ≤ φ₁) :
    frequencyEvenMoment
      (firstNextDomain k P (P^(1-(k : ℝ)*φ₁)) P (2*P^(1-φ₁)) R (P^φ₁) (P^φ₂))
      (aggregateNextPhase k (fun c : (ℕ × ℕ) × ℕ => firstParameters c.1)
        (fun c => (c.2 : ℤ))) r ≤ secondMoment k r φ₁ φ₂ P R := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  apply first_next_moment_le_second k r hPp.le (Real.rpow_nonneg hPp.le _)
    (Real.rpow_pos_of_pos hPp _) (by linarith) le_rfl
  · exact le_of_eq (by rw [mul_div_assoc,power_height hPp])
  · linarith
  · have hq : P^(1-φ₁) ≤ P := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hP (show 1-φ₁ ≤ 1 by linarith)
    linarith

theorem secondCross_le_A (k u r v w : ℕ) {φ₁ φ₂ P R a b c : ℝ}
    (hP : 1 ≤ P) (hφ₁ : 0 ≤ φ₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 2*(r : ℝ)*a=1) (hsmooth : (v : ℝ)*b+(w : ℝ)*c=(u : ℝ)) :
    secondCross k u φ₁ φ₂ P R ≤
      (secondMoment k r φ₁ φ₂ P R)^a*
        (smoothMoment k (2*v) (2*P^(1-φ₁-φ₂)) R)^b*
        (smoothMoment k (2*w) (2*P^(1-φ₁-φ₂)) R)^c := by
  apply (nextSmoothCrossIntegral_le_A k u r v w _ _ _ _ _ _ ha hb hc hsum haux hsmooth).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply Real.rpow_le_rpow _ (first_next_moment_le_second_scale k r hP hφ₁) ha
  rw [frequencyEvenMoment_eq_card]
  positivity

theorem secondCross_le_B (k u r v t : ℕ) {φ₁ φ₂ P R a b c : ℝ}
    (hP : 1 ≤ P) (hφ₁ : 0 ≤ φ₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 2*(r : ℝ)*a+2*(v : ℝ)*b=1) (hsmooth : (t : ℝ)*c=(u : ℝ)) :
    secondCross k u φ₁ φ₂ P R ≤
      (secondMoment k r φ₁ φ₂ P R)^a*(secondMoment k v φ₁ φ₂ P R)^b*
        (smoothMoment k (2*t) (2*P^(1-φ₁-φ₂)) R)^c := by
  apply (nextSmoothCrossIntegral_le_B k u r v t _ _ _ _ _ _ ha hb hc hsum haux hsmooth).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  have hm (r : ℕ) : 0 ≤ frequencyEvenMoment
      (firstNextDomain k P (P^(1-(k : ℝ)*φ₁)) P (2*P^(1-φ₁)) R (P^φ₁) (P^φ₂))
      (aggregateNextPhase k (fun c : (ℕ × ℕ) × ℕ => firstParameters c.1)
        (fun c => (c.2 : ℤ))) r := by
    rw [frequencyEvenMoment_eq_card]
    positivity
  exact mul_le_mul
    (Real.rpow_le_rpow (hm r) (first_next_moment_le_second_scale k r hP hφ₁) ha)
    (Real.rpow_le_rpow (hm v) (first_next_moment_le_second_scale k v hP hφ₁) hb)
    (Real.rpow_nonneg (hm v) _) (Real.rpow_nonneg (secondMoment_nonneg ..) _)

theorem ninth_A_second_cross {u v w : ℕ} {φ₁ φ₂ a b c lamv lamw : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/9) (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/9)
    (hv : AdmissibleExponent 9 (2*v) lamv) (hw : AdmissibleExponent 9 (2*w) lamw)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 4*a=1) (hsmooth : (v : ℝ)*b+(w : ℝ)*c=(u : ℝ)) :
    SourcePowerBound (secondCross 9 u φ₁ φ₂)
      ((8-24*(φ₁+φ₂))*a+((1-φ₁-φ₂)*lamv)*b+((1-φ₁-φ₂)*lamw)*c) := by
  have hq0 : 0 ≤ 1-φ₁-φ₂ := by linarith
  have hq1 : 1-φ₁-φ₂ ≤ 1 := by linarith
  have hF := (ninth_fourth_power hφ₁ hφ₁k hφ₂ hφ₂k).rpow ha
    (fun P R _ _ => secondMoment_nonneg ..)
  have hV := (admissible_shorter_source_bound hv (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1).rpow hb
    (fun P R _ _ => smoothMoment_nonneg ..)
  have hW := (admissible_shorter_source_bound hw (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1).rpow hc
    (fun P R _ _ => smoothMoment_nonneg ..)
  apply ((hF.mul hV).mul hW).of_le
    (fun P R _ _ => secondCross_nonneg ..)
  intro P R hP hR
  exact secondCross_le_A 9 u 2 v w hP hφ₁ ha hb hc hsum (by norm_num; exact haux) hsmooth

theorem ninth_B_second_cross {u t : ℕ} {φ₁ φ₂ a b c lam : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/9) (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/9)
    (ht : AdmissibleExponent 9 (2*t) lam)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 2*a+4*b=1) (hsmooth : (t : ℝ)*c=(u : ℝ)) :
    SourcePowerBound (secondCross 9 u φ₁ φ₂)
      ((3-8*(φ₁+φ₂))*a+(8-24*(φ₁+φ₂))*b+((1-φ₁-φ₂)*lam)*c) := by
  have hq0 : 0 ≤ 1-φ₁-φ₂ := by linarith
  have hq1 : 1-φ₁-φ₂ ≤ 1 := by linarith
  have hF := (ninth_second_power hφ₁ hφ₁k hφ₂ hφ₂k).rpow ha
    (fun P R _ _ => secondMoment_nonneg ..)
  have hG := (ninth_fourth_power hφ₁ hφ₁k hφ₂ hφ₂k).rpow hb
    (fun P R _ _ => secondMoment_nonneg ..)
  have hU := (admissible_shorter_source_bound ht (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1).rpow hc
    (fun P R _ _ => smoothMoment_nonneg ..)
  apply ((hF.mul hG).mul hU).of_le
    (fun P R _ _ => secondCross_nonneg ..)
  intro P R hP hR
  exact secondCross_le_B 9 u 1 2 t hP hφ₁ ha hb hc hsum (by norm_num; exact haux) hsmooth

#print axioms ninth_A_second_cross
#print axioms ninth_B_second_cross
end Waring.SeedCompletionSecondScales
