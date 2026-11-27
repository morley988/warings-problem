import Waring.SeedCompletionEvenDoubleBox
import Waring.SeedCompletionNinthDoubleSource

/-! # The literal even-degree j=2 source second moment

Both coefficient blocks vary. Their product cardinality is bounded at
P^(1/3), making the proved uniform curve error no larger than the diagonal.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenDoubleSource
open SeedCompletionEvenDouble SeedCompletionEvenDoubleBox FirstDifferenceSecond
  CoefficientPower SmoothMoments
open SeedCompletionNinthDoubleSource (sourceHeights sourceCoefficients sourceCenters
  sourceHeights_card_le sourceCoefficients_card_le sourceCenters_card_le block_card_le)

def sourceEvenSecondSum (d : ℕ) (P H₁ H₂ Q R M₁ M₂ α : ℝ) : ℂ :=
  actualSum d (sourceHeights H₁ H₂) (sourceCoefficients Q R M₁ M₂) (sourceCenters P) α

/-- The genuine source second moment with the coefficient-volume condition
shown explicitly, before choosing a common smoothness exponent. -/
theorem source_second_moment_of_volume (d : ℕ) (hd : supportedHalfDegree d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ R → M₁*R ≤ 4*P → M₂*R ≤ 4*P →
      M₁*M₂*R^2 ≤ P^(1/3 : ℝ) → R ≤ P^(ε/4) →
      (∫ α in (0 : ℝ)..1, ‖sourceEvenSecondSum d P H₁ H₂ Q R M₁ M₂ α‖^2) ≤
        C*P^(1+ε)*H₁*H₂*M₁*M₂ := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_second_diagonal_size d hd
    4 (by norm_num) (show 0 < ε/2 by positivity)
  refine ⟨2*C,by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₂ hR hM₁R hM₂R hvolume hsmall
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH₁0 : 0 ≤ H₁ := zero_le_one.trans hH₁
  have hH₂0 : 0 ≤ H₂ := zero_le_one.trans hH₂
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hHpos : ∀ h ∈ sourceHeights H₁ H₂, 0 < h.1 ∧ 0 < h.2 := by
    intro h hh
    rcases Finset.mem_product.mp hh with ⟨h1,h2⟩
    exact ⟨(Finset.mem_Icc.mp h1).1,(Finset.mem_Icc.mp h2).1⟩
  have hBpos : ∀ m ∈ sourceCoefficients Q R M₁ M₂, 0 < m.1 ∧ 0 < m.2 := by
    intro m hm
    rcases Finset.mem_product.mp hm with ⟨h1,h2⟩
    exact ⟨(mem_smoothNumbers.mp (Finset.mem_filter.mp h1).1).1.1,
      (mem_smoothNumbers.mp (Finset.mem_filter.mp h2).1).1.1⟩
  have hZpos : ∀ z ∈ sourceCenters P, 0 < z :=
    fun z hz => (Finset.mem_Icc.mp hz).1
  have hHbox : ∀ h ∈ sourceHeights H₁ H₂, (h.1 : ℝ) ≤ 4*P ∧ (h.2 : ℝ) ≤ 4*P := by
    intro h hh
    rcases Finset.mem_product.mp hh with ⟨h1,h2⟩
    have hb1 := (Nat.cast_le.mpr (Finset.mem_Icc.mp h1).2).trans
      (Nat.floor_le (by positivity : 0 ≤ 2*H₁))
    have hb2 := (Nat.cast_le.mpr (Finset.mem_Icc.mp h2).2).trans (Nat.floor_le hH₂0)
    exact ⟨by linarith,by linarith⟩
  have hBbox : ∀ m ∈ sourceCoefficients Q R M₁ M₂, (m.1 : ℝ) ≤ 4*P ∧ (m.2 : ℝ) ≤ 4*P := by
    intro m hm
    rcases Finset.mem_product.mp hm with ⟨h1,h2⟩
    exact ⟨((Finset.mem_filter.mp h1).2.2).trans hM₁R,
      ((Finset.mem_filter.mp h2).2.2).trans hM₂R⟩
  have hZbox : ∀ z ∈ sourceCenters P, (z : ℝ) ≤ 4*P := by
    intro z hz
    exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hz).2).trans (Nat.floor_le (by positivity))
  have hBcard := sourceCoefficients_card_le (Q := Q) hR0 hM₁0 hM₂0
  have hb := hbound P hPP₀ (sourceHeights H₁ H₂) (sourceCoefficients Q R M₁ M₂)
    (sourceCenters P) hHpos hBpos hZpos hHbox hBbox hZbox
    (hBcard.trans hvolume) (sourceCenters_card_le hPpos.le)
  change (∫ α in (0 : ℝ)..1, ‖sourceEvenSecondSum d P H₁ H₂ Q R M₁ M₂ α‖^2) ≤ _ at hb
  have hR2 : R^2 ≤ P^(ε/2) := by
    calc
      _ ≤ (P^(ε/4))^2 := pow_le_pow_left₀ hR0 hsmall 2
      _ = P^(ε/2) := by rw [← Real.rpow_mul_natCast hPpos.le]; congr 1; norm_num; ring
  calc
    _ ≤ C*P^(1+ε/2)*((sourceHeights H₁ H₂).card : ℝ)*
        ((sourceCoefficients Q R M₁ M₂).card : ℝ) := hb
    _ ≤ C*P^(1+ε/2)*(2*H₁*H₂)*(M₁*M₂*R^2) := by
      gcongr
      exact sourceHeights_card_le hH₁0 hH₂0
    _ ≤ C*P^(1+ε/2)*(2*H₁*H₂)*(M₁*M₂*P^(ε/2)) := by gcongr
    _ = _ := by
      rw [Real.rpow_add hPpos,show ε=ε/2+ε/2 by ring,Real.rpow_add hPpos,
        Real.rpow_add hPpos,Real.rpow_one]
      ring

/-- The source second-moment shape in each supported even degree. Both
coefficient scales may be as large as P^(1/8), which includes the actual
P^(1/k) ranges for degrees eight, sixteen and eighteen. -/
theorem source_even_second_second_moment (d : ℕ) (hd : supportedHalfDegree d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → M₁ ≤ P^(1/8 : ℝ) → 1 ≤ M₂ → M₂ ≤ P^(1/8 : ℝ) →
      1 ≤ R → R ≤ P^(min (ε/4) (1/24 : ℝ)) →
      (∫ α in (0 : ℝ)..1, ‖sourceEvenSecondSum d P H₁ H₂ Q R M₁ M₂ α‖^2) ≤
        C*P^(1+ε)*H₁*H₂*M₁*M₂ := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_second_moment_of_volume d hd hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hsmall
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hRpow : R ≤ P^(1/24 : ℝ) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_right _ _))
  have hReps : R ≤ P^(ε/4) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hproduct (M : ℝ) (hM : 0 ≤ M) (hMP : M ≤ P^(1/8 : ℝ)) : M*R ≤ 4*P := by
    calc
      _ ≤ P^(1/8 : ℝ)*P^(1/24 : ℝ) := mul_le_mul hMP hRpow hR0 (Real.rpow_nonneg hPpos.le _)
      _ = P^(1/6 : ℝ) := by rw [← Real.rpow_add hPpos]; norm_num
      _ ≤ P^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _ ≤ 4*P := by rw [Real.rpow_one]; linarith
  have hvolume : M₁*M₂*R^2 ≤ P^(1/3 : ℝ) := by
    calc
      _ ≤ (P^(1/8 : ℝ)*P^(1/8 : ℝ))*(P^(1/24 : ℝ))^2 := by gcongr
      _ = P^(1/4 : ℝ)*P^(1/12 : ℝ) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le]
        norm_num
      _ = P^(1/3 : ℝ) := by rw [← Real.rpow_add hPpos]; norm_num
  exact hbound P hPP₀ H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₂ hR
    (hproduct M₁ hM₁0 hM₁P) (hproduct M₂ hM₂0 hM₂P) hvolume hReps

#print axioms source_second_moment_of_volume
#print axioms source_even_second_second_moment
end Waring.SeedCompletionEvenDoubleSource
