import Waring.FirstStageAdmissibility
import Waring.SeedCompletionNinthFirst
import Waring.SeedCompletionNinthFourthBounds

/-!
# Actual first-stage auxiliary estimates in a common interface

The second moment is proved in degrees8,9,16,18. The fourth moment is
proved in degree9. Each bound retains the original floor-box variables.
-/

noncomputable section
namespace Waring.FirstStageTransport
open FirstDifferenceSecond SmoothMoments

def SupportedFirstDegree (k : ℕ) : Prop := k=8 ∨ k=9 ∨ k=16 ∨ k=18

theorem source_second_even (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H R M : ℝ, 1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ 2*P → R ≤ P^(ε/2) →
      frequencyEvenMoment (sourceFirstDomain P H P R M) (firstFrequency (2*d)) 1 ≤
        C*P^(1+ε)*M*H := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_first_second_moment d hd hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hP H R M hH hHP hM hR hMR hRP
  simpa only [frequencyEvenMoment,firstFrequency,sourceFirstSum,mul_one] using
    hbound P hP H P R M hH hHP hM hR hMR hRP

theorem source_second_supported (k : ℕ) (hk : SupportedFirstDegree k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H R M : ℝ, 1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ 2*P → R ≤ P^(ε/2) →
      frequencyEvenMoment (sourceFirstDomain P H P R M) (firstFrequency k) 1 ≤
        C*P^(1+ε)*M*H := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact source_second_even 4 (by simp [supportedHalfDegree]) hε
  · obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
      SeedCompletionNinthFirst.source_ninth_first_second_moment hε
    refine ⟨C,hC,P₀,hP₀,?_⟩
    intro P hP H R M hH hHP hM hR hMR hRP
    simpa only [frequencyEvenMoment,firstFrequency,
      SeedCompletionNinthFirst.sourceNinthFirstSum,mul_one] using
      hbound P hP H P R M hH hHP hM hR hMR hRP
  · exact source_second_even 8 (by simp [supportedHalfDegree]) hε
  · exact source_second_even 9 (by simp [supportedHalfDegree]) hε

theorem source_fourth_ninth {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H R M : ℝ, 1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ 2*P → R ≤ P^(ε/6) →
      frequencyEvenMoment (sourceFirstDomain P H P R M) (firstFrequency 9) 2 ≤
        C*P^(2+ε)*M^3*H^3 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionNinthFourthBounds.source_ninth_first_fourth_moment hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hP H R M hH hHP hM hR hMR hRP
  simpa only [frequencyEvenMoment,firstFrequency,
    SeedCompletionNinthFirst.sourceNinthFirstSum] using
    hbound P hP H P R M hH hHP hM hR hMR hRP

#print axioms source_second_supported
#print axioms source_fourth_ninth
end Waring.FirstStageTransport
