import Waring.SeedCompletionSecondScales
import Waring.SeedCompletionEvenSecondFourthSource

/-! # Proved even second-stage terminal bounds at fixed power scales

Both old coefficient blocks, source floors and fixed source dilations are
retained by the generic source-to-scale transport. The coefficient range
P^(1/(2*d)) is contained in the proved P^(1/8) range in every supported degree.
-/

noncomputable section
namespace Waring.SeedCompletionSecondScales
open SmoothMoments SeedCompletionSourceBounds SeedCompletionSecondTransport
open PolicyCompletionHolder FirstDifferenceSecond

theorem even_half_reciprocal_le (d : ℕ) (hd : supportedHalfDegree d) :
    1/((2*d : ℕ) : ℝ) ≤ 1/8 := by
  rcases hd with rfl | rfl | rfl <;> norm_num

theorem even_second_power (d : ℕ) (hd : supportedHalfDegree d) {φ₁ φ₂ : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/((2*d : ℕ) : ℝ))
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/((2*d : ℕ) : ℝ)) :
    SourcePowerBound (secondMoment (2*d) 1 φ₁ φ₂)
      (3-(2*(d : ℝ)-1)*(φ₁+φ₂)) := by
  have hk : 0 < 2*d := by rcases hd with rfl | rfl | rfl <;> omega
  have H := second_source_power_of_terminal (k := 2*d) (r := 1) (j := 1) (d := 1)
    (T := 4) (ρ := 1/24) hk (by norm_num) (by norm_num)
    hφ₁ hφ₁k hφ₂ hφ₂k ?_
  · convert H using 1 <;> push_cast <;> ring
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionEvenDoubleSource.source_even_second_second_moment d hd hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hRP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hm₁ := hM₁P.trans (Real.rpow_le_rpow_of_exponent_le hP (even_half_reciprocal_le d hd))
  have hm₂ := hM₂P.trans (Real.rpow_le_rpow_of_exponent_le hP (even_half_reciprocal_le d hd))
  simpa only [frequencyEvenMoment,show 2*1=2 by norm_num,pow_one] using
    hbound P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hm₁ hM₂ hm₂ hR hRP

theorem even_fourth_power (d : ℕ) (hd : supportedHalfDegree d) {φ₁ φ₂ : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/((2*d : ℕ) : ℝ))
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/((2*d : ℕ) : ℝ)) :
    SourcePowerBound (secondMoment (2*d) 2 φ₁ φ₂)
      (8-3*(2*(d : ℝ)-1)*(φ₁+φ₂)) := by
  have hk : 0 < 2*d := by rcases hd with rfl | rfl | rfl <;> omega
  have H := second_source_power_of_terminal (k := 2*d) (r := 2) (j := 3) (d := 2)
    (T := 12) (ρ := 1/24) hk (by norm_num) (by norm_num)
    hφ₁ hφ₁k hφ₂ hφ₂k ?_
  · convert H using 1 <;> push_cast <;> ring
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionEvenSecondFourthSource.source_even_second_fourth_moment d hd hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hRP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hm₁ := hM₁P.trans (Real.rpow_le_rpow_of_exponent_le hP (even_half_reciprocal_le d hd))
  have hm₂ := hM₂P.trans (Real.rpow_le_rpow_of_exponent_le hP (even_half_reciprocal_le d hd))
  simpa only [frequencyEvenMoment,show 2*2=4 by norm_num] using
    hbound P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hm₁ hM₂ hm₂ hR hRP

#print axioms even_second_power
#print axioms even_fourth_power
end Waring.SeedCompletionSecondScales
