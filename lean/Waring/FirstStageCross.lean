import Waring.FirstStageTerminals

/-!
# Actual exponents for the first cross integral

The proved auxiliary moments combine with genuinely admissible shorter
smooth moments. The extraction scale and every small-smoothness condition
are verified at the original height.
-/

noncomputable section
namespace Waring.FirstStageTransport
open FirstDifferenceSecond SmoothMoments

theorem first_stage_scales {k : ℕ} (hk : 2 ≤ k) {φ P : ℝ}
    (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1) (hP : 1 ≤ P) :
    1 ≤ P^φ ∧ P^φ ≤ P ∧ 1 ≤ P/(P^φ)^k ∧ P/(P^φ)^k ≤ 2*P ∧
    P/(P^φ)^k=P^(1-φ*(k : ℝ)) ∧
    ∀ R : ℝ, R ≤ P^(1/2 : ℝ) → P^φ*R ≤ 2*P := by
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hφhalf : φ ≤ 1/2 := by nlinarith
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH : P/(P^φ)^k=P^(1-φ*(k : ℝ)) := by
    rw [← Real.rpow_mul_natCast hPpos.le,Real.rpow_sub hPpos,Real.rpow_one]
  have hM := Real.one_le_rpow hP hφ0
  have hMP : P^φ ≤ P := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hP (show φ ≤ 1 by linarith)
  refine ⟨hM,hMP,?_,?_,hH,?_⟩
  · rw [hH]
    exact Real.one_le_rpow hP (by linarith)
  · rw [hH]
    have h : P^(1-φ*(k : ℝ)) ≤ P := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
        (show 1-φ*(k : ℝ) ≤ 1 by nlinarith)
    linarith
  · intro R hR
    calc
      _ ≤ P^φ*P^(1/2 : ℝ) := mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hPpos.le _)
      _ = P^(φ+1/2) := (Real.rpow_add hPpos _ _).symm
      _ ≤ P := by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hP (show φ+1/2 ≤ 1 by linarith)
      _ ≤ 2*P := by linarith

theorem crossExponent_second {k s : ℕ} (hk : SupportedFirstDegree k)
    {φ mu : ℝ} (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1)
    (hmu : AdmissibleExponent k (4*s) mu) :
    CrossExponent k s φ (1+mu/2+(1-(k : ℝ)-mu)*φ/2) := by
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  intro ε hε
  obtain ⟨C₀,hC₀,P₀,hP₀,hF⟩ := source_second_supported k hk hε
  obtain ⟨η₁,hη₁,C₁,hC₁,hG⟩ := admissibleExponent_uniform_shorter hmu hε
  let η : ℝ := min η₁ (min (ε/2) (1/2))
  have hη : 0 < η := lt_min hη₁ (lt_min (by positivity) (by norm_num))
  refine ⟨η,hη,C₀^(1/2 : ℝ)*C₁^(1/2 : ℝ),by positivity,P₀,hP₀,?_⟩
  intro P hPP R hR hRP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR₁ : R ≤ P^η₁ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hRε : R ≤ P^(ε/2) := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_left _ _)))
  have hRhalf : R ≤ P^(1/2 : ℝ) := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hM,hMP,hH,hHP,hHeq,hMR⟩ := first_stage_scales hk2 hφ0 hφk hP
  have hF' : frequencyEvenMoment (sourceFirstDomain P (P/(P^φ)^k) P R (P^φ))
      (firstFrequency k) 1 ≤ C₀*P^(2+ε+(1-(k : ℝ))*φ) := by
    calc
      _ ≤ C₀*P^(1+ε)*(P^φ)*(P/(P^φ)^k) :=
        hF P hPP (P/(P^φ)^k) R (P^φ) hH hHP hM hR (hMR R hRhalf) hRε
      _ = _ := by
        rw [hHeq]
        calc
          _ = C₀*(P^(1+ε)*P^φ*P^(1-φ*(k : ℝ))) := by ring
          _ = _ := by
            rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos]
            congr 2
            ring
  have hY : 1 ≤ P/P^φ := (one_le_div (Real.rpow_pos_of_pos hPpos _)).mpr hMP
  have hYP : P/P^φ ≤ P := div_le_self hPpos.le hM
  have hG' : smoothMoment k (4*s) (P/P^φ) R ≤ C₁*P^(ε+(1-φ)*mu) := by
    have h := hG P hP R hR hR₁ (P/P^φ) hY hYP
    rw [rpow_quotient_scale hPpos,mul_assoc,← Real.rpow_add hPpos] at h
    exact h
  calc
    _ ≤ (frequencyEvenMoment (sourceFirstDomain P (P/(P^φ)^k) P R (P^φ))
        (firstFrequency k) 1)^(1/2 : ℝ)*(smoothMoment k (4*s) (P/P^φ) R)^(1/2 : ℝ) :=
      firstCross_le_source_second k s hP hM
    _ ≤ (C₀*P^(2+ε+(1-(k : ℝ))*φ))^(1/2 : ℝ)*
        (C₁*P^(ε+(1-φ)*mu))^(1/2 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (frequencyEvenMoment_nonneg ..) hF' (by norm_num))
        (Real.rpow_le_rpow (smoothMoment_nonneg ..) hG' (by norm_num))
        (Real.rpow_nonneg (smoothMoment_nonneg ..) _) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hC₀.le (Real.rpow_nonneg hPpos.le _),
        Real.mul_rpow hC₁.le (Real.rpow_nonneg hPpos.le _),
        ← Real.rpow_mul hPpos.le,← Real.rpow_mul hPpos.le]
      calc
        _ = (C₀^(1/2 : ℝ)*C₁^(1/2 : ℝ))*
            (P^((2+ε+(1-(k : ℝ))*φ)*(1/2))*P^((ε+(1-φ)*mu)*(1/2))) := by ring
        _ = _ := by rw [← Real.rpow_add hPpos]; congr 2; ring

#print axioms crossExponent_second
end Waring.FirstStageTransport
