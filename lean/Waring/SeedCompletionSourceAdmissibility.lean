import Waring.SeedCompletionSourceBounds
import Waring.FirstStageAdmissibility

/-! # Pure smooth admissibility from the absorbed-source smoothness convention

Only the actual pure even moment is extended to smaller smoothness cutoffs.
Cross integrals retain a fixed maximal power cutoff, where the source
absorption theorem has been proved.
-/
noncomputable section
namespace Waring.SeedCompletionSourceBounds
open SmoothMoments FirstStageTransport

theorem first_stage_admissible_source {k s : ℕ} (hk : 0 < k) {lam φ χ θ : ℝ}
    (hlam : AdmissibleExponent k (2*(s+1)) lam)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hcross : SourcePowerBound (fun P R => firstCross k (s+1) P R (P^φ)) χ)
    (hbad : 1+φ+lam ≤ θ)
    (hdiag : 1+lam+(2*((s : ℝ)+1)-lam)*φ ≤ θ)
    (hnext : (2*(s : ℝ)+1)*φ+χ ≤ θ) :
    AdmissibleExponent k (2*(s+2)) θ := by
  apply admissible_of_source_bound
  intro ε hε
  let δ : ℝ := ε/(2*(s : ℝ)+4)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*(2*(s : ℝ)+4)=ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by positivity)
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have h2δε : 2*δ ≤ ε := by nlinarith
  obtain ⟨C₀,hC₀,P₀,hP₀,hrec⟩ := first_stage_recurrence k s hk hδ
  obtain ⟨η₁,hη₁,C₁,hC₁,hbound⟩ := admissibleExponent_uniform_shorter hlam hδ
  obtain ⟨η₂,hη₂,hX⟩ := hcross δ hδ
  refine ⟨min η₁ (min η₂ δ),lt_min hη₁ (lt_min hη₂ hδ),?_⟩
  intro η hη hηle
  obtain ⟨C₂,hC₂,P₂,hP₂,hX⟩ := hX η hη (hηle.trans ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨C₀*(2*C₁+C₂),by positivity,max P₀ P₂,
    hP₀.trans (le_max_left _ _),?_⟩
  intro P hPP
  let R : ℝ := P^η
  have hP1 : 1 ≤ P := hP₀.trans ((le_max_left _ _).trans hPP)
  have hR : 1 ≤ R := Real.one_le_rpow hP1 hη.le
  have hRP : R ≤ P^η := le_rfl
  rw [abs_of_nonneg (smoothMoment_nonneg ..)]
  have hPP₀ := (le_max_left P₀ P₂).trans hPP
  have hPP₂ := (le_max_right P₀ P₂).trans hPP
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR₁ : R ≤ P^η₁ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (hηle.trans (min_le_left _ _)))
  have hR₂ : R ≤ P^η₂ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (hηle.trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hRδ : R ≤ P^δ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (hηle.trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hM : 1 ≤ P^φ := Real.one_le_rpow hP hφ0
  have hMP : P^φ ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hφ1
  have hMpos : 0 < P^φ := Real.rpow_pos_of_pos hPpos _
  have hY : 1 ≤ P/P^φ := (one_le_div hMpos).mpr hMP
  have hYP : P/P^φ ≤ P := div_le_self hPpos.le hM
  have hJ := hbound P hP R hR hR₁ P hP le_rfl
  have hJ' := hbound P hP R hR hR₁ (P/P^φ) hY hYP
  have hcross' : firstCross k (s+1) P R (P^φ) ≤ C₂*P^(χ+δ) :=
    (le_abs_self _).trans (hX P hPP₂)
  have h₁ : P^φ*P^(1+δ)*smoothMoment k (2*(s+1)) P R ≤ C₁*P^(θ+ε) := by
    calc
      _ ≤ P^φ*P^(1+δ)*(C₁*P^δ*P^lam) := by gcongr
      _ = C₁*P^(φ+(1+δ)+δ+lam) := by
        calc
          _ = C₁*(P^φ*P^(1+δ)*P^δ*P^lam) := by ring
          _ = _ := by rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos,← Real.rpow_add hPpos]
      _ ≤ C₁*P^(θ+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hC₁.le
  have h₂ : P^(1+δ)*(P^φ*R)^(2*(s+1))*smoothMoment k (2*(s+1)) (P/P^φ) R ≤
      C₁*P^(θ+ε) := by
    calc
      _ ≤ P^(1+δ)*(P^φ*P^δ)^(2*(s+1))*(C₁*P^δ*(P/P^φ)^lam) := by
        gcongr
        exact smoothMoment_nonneg ..
      _ = C₁*P^((1+δ)+(φ+δ)*(2*((s : ℝ)+1))+δ+(1-φ)*lam) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le,
          rpow_quotient_scale hPpos]
        push_cast
        calc
          _ = C₁*(P^(1+δ)*P^((φ+δ)*(2*((s : ℝ)+1)))*P^δ*P^((1-φ)*lam)) := by ring
          _ = _ := by rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos,← Real.rpow_add hPpos]
      _ ≤ C₁*P^(θ+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)) hC₁.le
  have h₃ : P^δ*(P^φ*R)^(2*s+1)*firstCross k (s+1) P R (P^φ) ≤ C₂*P^(θ+ε) := by
    calc
      _ ≤ P^δ*(P^φ*P^δ)^(2*s+1)*(C₂*P^(χ+δ)) := by
        gcongr
        exact firstCross_nonneg ..
      _ = C₂*P^(δ+(φ+δ)*(2*(s : ℝ)+1)+(χ+δ)) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le]
        push_cast
        calc
          _ = C₂*(P^δ*P^((φ+δ)*(2*(s : ℝ)+1))*P^(χ+δ)) := by ring
          _ = _ := by rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos]
      _ ≤ C₂*P^(θ+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by
          have he : δ+(φ+δ)*(2*(s : ℝ)+1)+(χ+δ) =
              ((2*(s : ℝ)+1)*φ+χ)+ε-δ := by rw [← hδε]; ring
          rw [he]
          linarith)) hC₂.le
  calc
    _ ≤ C₀*(P^φ*P^(1+δ)*smoothMoment k (2*(s+1)) P R+
        P^(1+δ)*(P^φ*R)^(2*(s+1))*smoothMoment k (2*(s+1)) (P/P^φ) R+
        P^δ*(P^φ*R)^(2*s+1)*firstCross k (s+1) P R (P^φ)) :=
      hrec P hPP₀ R (P^φ) hR hM
    _ ≤ C₀*(C₁*P^(θ+ε)+C₁*P^(θ+ε)+C₂*P^(θ+ε)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃) hC₀.le
    _ = _ := by ring

#print axioms first_stage_admissible_source
end Waring.SeedCompletionSourceBounds
