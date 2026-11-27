import Waring.SeedCompletionFirstUpdates
import Waring.SeedCompletionTerminalThree
import Waring.SeedCompletionSourceAdmissibility
import Waring.SeedCompletionScaleAlgebra

/-! # The actual first A terminal at arbitrary adjacent smooth orders -/
noncomputable section
namespace Waring.SeedCompletionFirstGeneralA
open SmoothMoments FirstStageTransport FirstDifferenceSecond
open SeedCompletionSourceBounds SeedCompletionTerminalThree
open SeedCompletionSharpBackward SeedCompletionBackwardAggregate PolicyCompletionHolder

def firstMoment (k r : ℕ) (φ P R : ℝ) : ℝ :=
  frequencyEvenMoment (sourceFirstDomain P (P^(1-(k : ℝ)*φ)) P R (P^φ))
    (firstFrequency k) r

theorem firstMoment_nonneg (k r : ℕ) (φ P R : ℝ) :
    0 ≤ firstMoment k r φ P R := by
  unfold firstMoment
  rw [frequencyEvenMoment_eq_card]
  positivity

theorem first_fourth_power {k : ℕ} (hk : SupportedFirstDegree k) {φ : ℝ}
    (hφ : 0 ≤ φ) (hφk : φ ≤ 1/(k : ℝ)) :
    SourcePowerBound (firstMoment k 2 φ) (5+3*(1-(k : ℝ))*φ) := by
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_fourth_supported k hk hε
  refine ⟨min (ε/6) (1/6),lt_min (by positivity) (by norm_num),?_⟩
  intro η hη hηle
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hk8 : 8 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk8R : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hkpos : 0 < (k : ℝ) := by linarith
  have hφmul : φ*(k : ℝ) ≤ 1 := (le_div_iff₀ hkpos).mp hφk
  have hφsixth : φ ≤ 1/6 := by nlinarith [mul_nonneg hφ (show 0 ≤ (k : ℝ)-6 by linarith)]
  have hH : 1 ≤ P^(1-(k : ℝ)*φ) := Real.one_le_rpow hP (by nlinarith)
  have hHP : P^(1-(k : ℝ)*φ) ≤ 2*P := by
    have H : P^(1-(k : ℝ)*φ) ≤ P := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
        (show 1-(k : ℝ)*φ ≤ 1 by nlinarith [mul_nonneg hkpos.le hφ])
    linarith
  have hM := Real.one_le_rpow hP hφ
  have hR := Real.one_le_rpow hP hη.le
  have hMR : P^φ*P^η ≤ P^(1/3 : ℝ) := by
    rw [← Real.rpow_add hPp]
    exact Real.rpow_le_rpow_of_exponent_le hP (by
      have H := hηle.trans (min_le_right _ _)
      linarith)
  have hRP : P^η ≤ P^(ε/6) :=
    Real.rpow_le_rpow_of_exponent_le hP (hηle.trans (min_le_left _ _))
  have H := hbound P hPP (P^(1-(k : ℝ)*φ)) (P^η) (P^φ) hH hHP hM hR hMR hRP
  rw [abs_of_nonneg (firstMoment_nonneg ..)]
  apply H.trans_eq
  rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_mul_natCast hPp.le]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = C*(P^(2+ε)*P^(φ*3)*P^((1-(k : ℝ)*φ)*3)) := by ring
    _ = _ := by rw [← Real.rpow_add hPp,← Real.rpow_add hPp]; congr 2; ring

theorem firstCross_le_A (k u v w : ℕ) {φ P R a b c : ℝ}
    (hP : 1 ≤ P) (hφ : 0 ≤ φ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 4*a=1) (hsmooth : (v : ℝ)*b+(w : ℝ)*c=(u : ℝ)) :
    firstCross k u P R (P^φ) ≤
      (firstMoment k 2 φ P R)^a*
        (smoothMoment k (2*v) (P^(1-φ)) R)^b*
        (smoothMoment k (2*w) (P^(1-φ)) R)^c := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have H := nextSmoothCrossIntegral_le_A k u 2 v w ({()} : Finset Unit)
    (fun _ => []) (CoefficientPower.coefficientBlock P R (P^φ))
    (⌊P⌋₊ : ℤ) (P/P^φ) R ha hb hc hsum (by norm_num; exact haux) hsmooth
  change firstCross k u P R (P^φ) ≤ _ at H
  have hQ : P/P^φ=P^(1-φ) := by rw [Real.rpow_sub hPp,Real.rpow_one]
  rw [hQ] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply Real.rpow_le_rpow _ _ ha
  · rw [frequencyEvenMoment_eq_card]; positivity
  · have H := initial_auxiliary_le_source k 2 (R := R) hP (Real.one_le_rpow hP hφ)
    rw [power_height hPp] at H
    exact H

theorem first_A_cross_power {k u v w : ℕ} (hk : SupportedFirstDegree k)
    {φ a b c lamv lamw : ℝ} (hφ : 0 ≤ φ) (hφk : φ ≤ 1/(k : ℝ))
    (hv : AdmissibleExponent k (2*v) lamv) (hw : AdmissibleExponent k (2*w) lamw)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 4*a=1) (hsmooth : (v : ℝ)*b+(w : ℝ)*c=(u : ℝ)) :
    SourcePowerBound (fun P R => firstCross k u P R (P^φ))
      ((5+3*(1-(k : ℝ))*φ)*a+((1-φ)*lamv)*b+((1-φ)*lamw)*c) := by
  have hk1 : 1 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hφ1 : φ ≤ 1 := hφk.trans ((div_le_one hkpos).mpr (by exact_mod_cast hk1))
  have hq0 : 0 ≤ 1-φ := by linarith
  have hq1 : 1-φ ≤ 1 := by linarith
  have hF := (first_fourth_power hk hφ hφk).rpow ha (fun P R _ _ => firstMoment_nonneg ..)
  have hV : SourcePowerBound (fun P R => (smoothMoment k (2*v) (P^(1-φ)) R)^b)
      (((1-φ)*lamv)*b) := by
    simpa only [one_mul] using
      (admissible_shorter_source_bound hv (le_refl (1 : ℝ)) hq0 hq1).rpow hb
        (fun P R _ _ => smoothMoment_nonneg ..)
  have hW : SourcePowerBound (fun P R => (smoothMoment k (2*w) (P^(1-φ)) R)^c)
      (((1-φ)*lamw)*c) := by
    simpa only [one_mul] using
      (admissible_shorter_source_bound hw (le_refl (1 : ℝ)) hq0 hq1).rpow hc
        (fun P R _ _ => smoothMoment_nonneg ..)
  apply ((hF.mul hV).mul hW).of_le (fun P R _ _ => firstCross_nonneg ..)
  intro P R hP hR
  exact firstCross_le_A k u v w hP hφ ha hb hc hsum haux hsmooth

#print axioms first_fourth_power
#print axioms first_A_cross_power
end Waring.SeedCompletionFirstGeneralA
