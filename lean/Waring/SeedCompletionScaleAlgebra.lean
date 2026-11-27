import Waring.SeedCompletionSourceBounds
import Waring.FirstStageAdmissibility

/-! # Exact power-scale identities and eventual source-bound transport -/
noncomputable section
namespace Waring.SeedCompletionSourceBounds
open SmoothMoments

theorem power_height {P : ℝ} (hP : 0 < P) (k : ℕ) (φ : ℝ) :
    P/(P^φ)^k=P^(1-(k : ℝ)*φ) := by
  rw [← Real.rpow_mul_natCast hP.le,Real.rpow_sub hP,Real.rpow_one]
  congr 2
  ring

theorem power_quotient {P : ℝ} (hP : 0 < P) (a b : ℝ) :
    P^a/P^b=P^(a-b) := (Real.rpow_sub hP a b).symm

theorem source_lower_smoothness {P η : ℝ} (hP : 4 ≤ P) (hη : 0 ≤ η) :
    (4*P)^(η/2) ≤ P^η := by
  have hPp : 0 < P := by linarith
  calc
    _ ≤ (P^2)^(η/2) := Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
    _ = P^η := by rw [← Real.rpow_natCast_mul hPp.le]; congr 1; norm_num; ring

theorem fixed_power_eventually_two {η : ℝ} (hη : 0 < η) :
    ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P → 2 ≤ P^η := by
  refine ⟨max 1 ((2 : ℝ)^(1/η)),le_max_left _ _,?_⟩
  intro P hPP
  calc
    (2 : ℝ) = ((2 : ℝ)^(1/η))^η := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),div_mul_cancel₀ _ hη.ne',Real.rpow_one]
    _ ≤ P^η := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hPP) hη.le

theorem SourcePowerBound.of_eventually_le {F G : ℝ → ℝ → ℝ} {a : ℝ}
    (hG : SourcePowerBound G a)
    (hdom : ∀ η : ℝ,0 < η → ∃ P₀ : ℝ,1 ≤ P₀ ∧
      ∀ P : ℝ,P₀ ≤ P → |F P (P^η)| ≤ |G P (P^η)|) :
    SourcePowerBound F a := by
  apply hG.of_epsilon_domination
  intro δ hδ
  refine ⟨1,by norm_num,?_⟩
  intro η hη hηle
  obtain ⟨P₀,hP₀,hbound⟩ := hdom η hη
  refine ⟨1,by norm_num,P₀,hP₀,?_⟩
  intro P hPP
  exact (hbound P hPP).trans (by
    rw [one_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_rpow (hP₀.trans hPP) hδ.le))

theorem SourcePowerBound.of_le {F G : ℝ → ℝ → ℝ} {a : ℝ}
    (hG : SourcePowerBound G a)
    (hF : ∀ P R : ℝ,1 ≤ P → 1 ≤ R → 0 ≤ F P R)
    (hle : ∀ P R : ℝ,1 ≤ P → 1 ≤ R → F P R ≤ G P R) :
    SourcePowerBound F a := by
  apply hG.of_eventually_le
  intro η hη
  refine ⟨1,le_rfl,?_⟩
  intro P hP
  have hR := Real.one_le_rpow hP hη.le
  rw [abs_of_nonneg (hF P _ hP hR)]
  exact (hle P _ hP hR).trans (le_abs_self _)

#print axioms SourcePowerBound.of_eventually_le
end Waring.SeedCompletionSourceBounds
