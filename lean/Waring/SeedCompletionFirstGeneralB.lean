import Waring.SeedCompletionFirstGeneralA

/-! # Actual first-stage B terminal with two auxiliary moments

The proved first second and fourth moments combine with an arbitrary
admissible smooth moment, using the exact B-process Holder weights.
-/

noncomputable section
namespace Waring.SeedCompletionFirstGeneralB
open SmoothMoments FirstStageTransport FirstDifferenceSecond
open SeedCompletionSourceBounds SeedCompletionTerminalThree SeedCompletionFirstGeneralA
open SeedCompletionSharpBackward SeedCompletionBackwardAggregate PolicyCompletionHolder

theorem first_second_power {k : ℕ} (hk : SupportedFirstDegree k) {φ : ℝ}
    (hφ : 0 ≤ φ) (hφk : φ ≤ 1/(k : ℝ)) :
    SourcePowerBound (firstMoment k 1 φ) (2+(1-(k : ℝ))*φ) := by
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_second_supported k hk hε
  refine ⟨min (ε/2) (1/2),lt_min (by positivity) (by norm_num),?_⟩
  intro η hη hηle
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : 0 < (k : ℝ) := by linarith
  have hφmul : φ*(k : ℝ) ≤ 1 := (le_div_iff₀ hkpos).mp hφk
  obtain ⟨hM,hMP,hH,hHP,hHeq,hMR⟩ := first_stage_scales hk2 hφ hφmul hP
  have hR := Real.one_le_rpow hP hη.le
  have hRP : P^η ≤ P^(ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hP (hηle.trans (min_le_left _ _))
  have hRhalf : P^η ≤ P^(1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP (hηle.trans (min_le_right _ _))
  have H := hbound P hPP (P/(P^φ)^k) (P^η) (P^φ) hH hHP hM hR (hMR _ hRhalf) hRP
  rw [power_height hPp] at H
  rw [abs_of_nonneg (firstMoment_nonneg ..)]
  apply H.trans_eq
  calc
    _ = C*(P^(1+ε)*P^φ*P^(1-(k : ℝ)*φ)) := by ring
    _ = _ := by rw [← Real.rpow_add hPp,← Real.rpow_add hPp]; congr 2; ring

theorem firstCross_le_B (k u t : ℕ) {φ P R a b c : ℝ}
    (hP : 1 ≤ P) (hφ : 0 ≤ φ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 2*a+4*b=1) (hsmooth : (t : ℝ)*c=(u : ℝ)) :
    firstCross k u P R (P^φ) ≤
      (firstMoment k 1 φ P R)^a*(firstMoment k 2 φ P R)^b*
        (smoothMoment k (2*t) (P^(1-φ)) R)^c := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have H := nextSmoothCrossIntegral_le_B k u 1 2 t ({()} : Finset Unit)
    (fun _ => []) (CoefficientPower.coefficientBlock P R (P^φ))
    (⌊P⌋₊ : ℤ) (P/P^φ) R ha hb hc hsum (by norm_num; exact haux) hsmooth
  change firstCross k u P R (P^φ) ≤ _ at H
  have hQ : P/P^φ=P^(1-φ) := by rw [Real.rpow_sub hPp,Real.rpow_one]
  rw [hQ] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply mul_le_mul
  · apply Real.rpow_le_rpow _ _ ha
    · rw [frequencyEvenMoment_eq_card]; positivity
    · have H := initial_auxiliary_le_source k 1 (R := R) hP (Real.one_le_rpow hP hφ)
      rw [power_height hPp] at H
      exact H
  · apply Real.rpow_le_rpow _ _ hb
    · rw [frequencyEvenMoment_eq_card]; positivity
    · have H := initial_auxiliary_le_source k 2 (R := R) hP (Real.one_le_rpow hP hφ)
      rw [power_height hPp] at H
      exact H
  · exact Real.rpow_nonneg (by rw [frequencyEvenMoment_eq_card]; positivity) _
  · exact Real.rpow_nonneg (firstMoment_nonneg ..) _

theorem first_B_cross_power {k u t : ℕ} (hk : SupportedFirstDegree k)
    {φ a b c lam : ℝ} (hφ : 0 ≤ φ) (hφk : φ ≤ 1/(k : ℝ))
    (ht : AdmissibleExponent k (2*t) lam)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a+b+c=1)
    (haux : 2*a+4*b=1) (hsmooth : (t : ℝ)*c=(u : ℝ)) :
    SourcePowerBound (fun P R => firstCross k u P R (P^φ))
      ((2+(1-(k : ℝ))*φ)*a+(5+3*(1-(k : ℝ))*φ)*b+((1-φ)*lam)*c) := by
  have hk1 : 1 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hφ1 : φ ≤ 1 := hφk.trans ((div_le_one hkpos).mpr (by exact_mod_cast hk1))
  have hq0 : 0 ≤ 1-φ := by linarith
  have hq1 : 1-φ ≤ 1 := by linarith
  have hF := (first_second_power hk hφ hφk).rpow ha (fun P R _ _ => firstMoment_nonneg ..)
  have hG := (first_fourth_power hk hφ hφk).rpow hb (fun P R _ _ => firstMoment_nonneg ..)
  have hU : SourcePowerBound (fun P R => (smoothMoment k (2*t) (P^(1-φ)) R)^c)
      (((1-φ)*lam)*c) := by
    simpa only [one_mul] using
      (admissible_shorter_source_bound ht (le_refl (1 : ℝ)) hq0 hq1).rpow hc
        (fun P R _ _ => smoothMoment_nonneg ..)
  apply ((hF.mul hG).mul hU).of_le (fun P R _ _ => firstCross_nonneg ..)
  intro P R hP hR
  exact firstCross_le_B k u t hP hφ ha hb hc hsum haux hsmooth

#print axioms first_second_power
#print axioms first_B_cross_power
end Waring.SeedCompletionFirstGeneralB
