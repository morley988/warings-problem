import Waring.FirstStageCross

/-! # The actual degree-nine fourth-moment terminal exponent -/

noncomputable section
namespace Waring.FirstStageTransport
open FirstDifferenceSecond SmoothMoments

theorem crossExponent_fourth_ninth {φ mu : ℝ} (hφ0 : 0 ≤ φ) (hφ9 : φ*9 ≤ 1)
    (hmu : AdmissibleExponent 9 8 mu) :
    CrossExponent 9 3 φ ((5+3*mu)/4+(-24-3*mu)*φ/4) := by
  intro ε hε
  obtain ⟨C₀,hC₀,P₀,hP₀,hF⟩ := source_fourth_ninth hε
  obtain ⟨η₁,hη₁,C₁,hC₁,hG⟩ := admissibleExponent_uniform_shorter hmu hε
  let η : ℝ := min η₁ (min (ε/6) (1/2))
  have hη : 0 < η := lt_min hη₁ (lt_min (by positivity) (by norm_num))
  refine ⟨η,hη,C₀^(1/4 : ℝ)*C₁^(3/4 : ℝ),by positivity,P₀,hP₀,?_⟩
  intro P hPP R hR hRP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR₁ : R ≤ P^η₁ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hRε : R ≤ P^(ε/6) := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_left _ _)))
  have hRhalf : R ≤ P^(1/2 : ℝ) := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hM,hMP,hH,hHP,hHeq,hMR⟩ := first_stage_scales (by norm_num : 2 ≤ (9 : ℕ))
    hφ0 (by exact_mod_cast hφ9) hP
  norm_num only [Nat.cast_ofNat] at hHeq
  have hF' : frequencyEvenMoment (sourceFirstDomain P (P/(P^φ)^9) P R (P^φ))
      (firstFrequency 9) 2 ≤ C₀*P^(5+ε-24*φ) := by
    calc
      _ ≤ C₀*P^(2+ε)*(P^φ)^3*(P/(P^φ)^9)^3 :=
        hF P hPP (P/(P^φ)^9) R (P^φ) hH hHP hM hR (hMR R hRhalf) hRε
      _ = _ := by
        rw [hHeq,← Real.rpow_mul_natCast hPpos.le,← Real.rpow_mul_natCast hPpos.le]
        norm_num only [Nat.cast_ofNat]
        calc
          _ = C₀*(P^(2+ε)*P^(φ*3)*P^((1-φ*9)*3)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos]
            congr 2
            ring
  have hY : 1 ≤ P/P^φ := (one_le_div (Real.rpow_pos_of_pos hPpos _)).mpr hMP
  have hYP : P/P^φ ≤ P := div_le_self hPpos.le hM
  have hG' : smoothMoment 9 8 (P/P^φ) R ≤ C₁*P^(ε+(1-φ)*mu) := by
    have h := hG P hP R hR hR₁ (P/P^φ) hY hYP
    rw [rpow_quotient_scale hPpos,mul_assoc,← Real.rpow_add hPpos] at h
    exact h
  calc
    _ ≤ (frequencyEvenMoment (sourceFirstDomain P (P/(P^φ)^9) P R (P^φ))
        (firstFrequency 9) 2)^(1/4 : ℝ)*(smoothMoment 9 8 (P/P^φ) R)^(3/4 : ℝ) :=
      firstCross_le_source_fourth 9 hP hM
    _ ≤ (C₀*P^(5+ε-24*φ))^(1/4 : ℝ)*(C₁*P^(ε+(1-φ)*mu))^(3/4 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (frequencyEvenMoment_nonneg ..) hF' (by norm_num))
        (Real.rpow_le_rpow (smoothMoment_nonneg ..) hG' (by norm_num))
        (Real.rpow_nonneg (smoothMoment_nonneg ..) _) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hC₀.le (Real.rpow_nonneg hPpos.le _),
        Real.mul_rpow hC₁.le (Real.rpow_nonneg hPpos.le _),
        ← Real.rpow_mul hPpos.le,← Real.rpow_mul hPpos.le]
      calc
        _ = (C₀^(1/4 : ℝ)*C₁^(3/4 : ℝ))*
            (P^((5+ε-24*φ)*(1/4))*P^((ε+(1-φ)*mu)*(3/4))) := by ring
        _ = _ := by rw [← Real.rpow_add hPpos]; congr 2; ring

#print axioms crossExponent_fourth_ninth
end Waring.FirstStageTransport
