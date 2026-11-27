import Waring.SeedCompletionEvenFourthSource
import Waring.FirstStageUpdates

/-! # Actual fourth-terminal exponent and A update in all four source degrees -/

noncomputable section
namespace Waring.FirstStageTransport
open FirstDifferenceSecond SmoothMoments

theorem source_fourth_even (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ H R M : ℝ,1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ P^(1/3 : ℝ) → R ≤ P^(ε/6) →
      frequencyEvenMoment (sourceFirstDomain P H P R M) (firstFrequency (2*d)) 2 ≤
        C*P^(2+ε)*M^3*H^3 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionEvenFourth.source_even_first_fourth_moment d hd hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hP H R M hH hHP hM hR hMR hRP
  simpa only [frequencyEvenMoment,firstFrequency,sourceFirstSum] using
    hbound P hP H P R M hH hHP hM hR hMR hRP

theorem source_fourth_supported (k : ℕ) (hk : SupportedFirstDegree k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ H R M : ℝ,1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ P^(1/3 : ℝ) → R ≤ P^(ε/6) →
      frequencyEvenMoment (sourceFirstDomain P H P R M) (firstFrequency k) 2 ≤
        C*P^(2+ε)*M^3*H^3 := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact source_fourth_even 4 (by simp [supportedHalfDegree]) hε
  · obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_fourth_ninth hε
    refine ⟨C,hC,P₀,hP₀,?_⟩
    intro P hPP H R M hH hHP hM hR hMR hRP
    have hP : 1 ≤ P := hP₀.trans hPP
    have hp : P^(1/3 : ℝ) ≤ P := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
        (show (1/3 : ℝ) ≤ 1 by norm_num)
    exact hbound P hPP H R M hH hHP hM hR (hMR.trans (hp.trans (by linarith))) hRP
  · exact source_fourth_even 8 (by simp [supportedHalfDegree]) hε
  · exact source_fourth_even 9 (by simp [supportedHalfDegree]) hε

theorem crossExponent_fourth_supported {k : ℕ} (hk : SupportedFirstDegree k)
    {φ mu : ℝ} (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1)
    (hmu : AdmissibleExponent k 8 mu) :
    CrossExponent k 3 φ ((5+3*mu)/4+(3-3*(k : ℝ)-3*mu)*φ/4) := by
  intro ε hε
  obtain ⟨C₀,hC₀,P₀,hP₀,hF⟩ := source_fourth_supported k hk hε
  obtain ⟨η₁,hη₁,C₁,hC₁,hG⟩ := admissibleExponent_uniform_shorter hmu hε
  let η : ℝ := min η₁ (min (ε/6) (1/6))
  have hη : 0 < η := lt_min hη₁ (lt_min (by positivity) (by norm_num))
  refine ⟨η,hη,C₀^(1/4 : ℝ)*C₁^(3/4 : ℝ),by positivity,P₀,hP₀,?_⟩
  intro P hPP R hR hRP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hk8 : 8 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk8R : 8 ≤ (k : ℝ) := by exact_mod_cast hk8
  have hφsixth : φ ≤ 1/6 := by nlinarith
  have hR₁ : R ≤ P^η₁ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hRε : R ≤ P^(ε/6) := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_left _ _)))
  have hRsixth : R ≤ P^(1/6 : ℝ) := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hM,hMP,hH,hHP,hHeq,hMR⟩ := first_stage_scales (by omega : 2 ≤ k)
    hφ0 hφk hP
  have hMRshort : P^φ*R ≤ P^(1/3 : ℝ) := by
    calc
      _ ≤ P^φ*P^(1/6 : ℝ) := mul_le_mul_of_nonneg_left hRsixth (by positivity)
      _ = P^(φ+1/6) := by rw [Real.rpow_add hPpos]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hF' : frequencyEvenMoment (sourceFirstDomain P (P/(P^φ)^k) P R (P^φ))
      (firstFrequency k) 2 ≤ C₀*P^(5+ε+(3-3*(k : ℝ))*φ) := by
    calc
      _ ≤ C₀*P^(2+ε)*(P^φ)^3*(P/(P^φ)^k)^3 :=
        hF P hPP (P/(P^φ)^k) R (P^φ) hH hHP hM hR hMRshort hRε
      _ = _ := by
        rw [hHeq,← Real.rpow_mul_natCast hPpos.le,← Real.rpow_mul_natCast hPpos.le]
        norm_num only [Nat.cast_ofNat]
        calc
          _ = C₀*(P^(2+ε)*P^(φ*3)*P^((1-φ*(k : ℝ))*3)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos]
            congr 2
            ring
  have hY : 1 ≤ P/P^φ := (one_le_div (Real.rpow_pos_of_pos hPpos _)).mpr hMP
  have hYP : P/P^φ ≤ P := div_le_self hPpos.le hM
  have hG' : smoothMoment k 8 (P/P^φ) R ≤ C₁*P^(ε+(1-φ)*mu) := by
    have h := hG P hP R hR hR₁ (P/P^φ) hY hYP
    rw [rpow_quotient_scale hPpos,mul_assoc,← Real.rpow_add hPpos] at h
    exact h
  calc
    _ ≤ (frequencyEvenMoment (sourceFirstDomain P (P/(P^φ)^k) P R (P^φ))
        (firstFrequency k) 2)^(1/4 : ℝ)*(smoothMoment k 8 (P/P^φ) R)^(3/4 : ℝ) :=
      firstCross_le_source_fourth k hP hM
    _ ≤ (C₀*P^(5+ε+(3-3*(k : ℝ))*φ))^(1/4 : ℝ)*
        (C₁*P^(ε+(1-φ)*mu))^(3/4 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (frequencyEvenMoment_nonneg ..) hF' (by norm_num))
        (Real.rpow_le_rpow (smoothMoment_nonneg ..) hG' (by norm_num))
        (Real.rpow_nonneg (smoothMoment_nonneg ..) _) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hC₀.le (Real.rpow_nonneg hPpos.le _),
        Real.mul_rpow hC₁.le (Real.rpow_nonneg hPpos.le _),
        ← Real.rpow_mul hPpos.le,← Real.rpow_mul hPpos.le]
      calc
        _ = (C₀^(1/4 : ℝ)*C₁^(3/4 : ℝ))*
            (P^((5+ε+(3-3*(k : ℝ))*φ)*(1/4))*P^((ε+(1-φ)*mu)*(3/4))) := by ring
        _ = _ := by rw [← Real.rpow_add hPpos]; congr 2; ring

/-- The source A_1^(4,2) update, with all analytic estimates discharged. -/
theorem admissible_eight_A_supported {k : ℕ} (hk : SupportedFirstDegree k)
    {lam mu φ : ℝ} (hlam : AdmissibleExponent k 6 lam) (hmu : AdmissibleExponent k 8 mu)
    (hlam5 : lam ≤ 5) (hφ0 : 0 ≤ φ) (hφk : φ*(k : ℝ) ≤ 1)
    (hbalance : 1+3*mu-4*lam ≤ (3*(k : ℝ)+1+3*mu-4*lam)*φ) :
    AdmissibleExponent k 8 (1+lam+(6-lam)*φ) := by
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk2R : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hφ1 : φ ≤ 1 := by nlinarith
  apply first_stage_admissible (s := 2) (by omega : 0 < k)
    hlam hφ0 hφ1 (crossExponent_fourth_supported hk hφ0 hφk hmu)
  · norm_num
    nlinarith
  · norm_num
  · norm_num
    nlinarith

#print axioms source_fourth_supported
#print axioms crossExponent_fourth_supported
#print axioms admissible_eight_A_supported
end Waring.FirstStageTransport
