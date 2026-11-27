import Waring.SeedCompletionNinthSecondFourth

/-! # Literal degree-nine j=2 fourth-moment terminal

All source floors, both coefficient blocks, doubled old height and the
full center interval are preserved. The remaining smoothness losses are
absorbed by a single explicit positive choice.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthSecondFourthSource
open SeedCompletionNinthSecondWeyl SeedCompletionNinthDoubleSource
open CoefficientPower SmoothMoments

theorem source_sum_eq_family (P H₁ H₂ Q R M₁ M₂ α : ℝ) :
    sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α =
      familySum (sourceHeights H₁ H₂ ×ˢ sourceCoefficients Q R M₁ M₂) ⌊4*P⌋₊ α := by
  rw [familySum_eq_actualSum]
  rfl

theorem source_fourth_moment_of_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ R → M₁*R ≤ 4*P → M₂*R ≤ 4*P →
      M₁*M₂*R^2 ≤ P^(1/3 : ℝ) → R ≤ P^(ε/12) →
      (∫ α in (0 : ℝ)..1,‖sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α‖^4) ≤
        C*P^(2+ε)*H₁^3*H₂^3*M₁^3*M₂^3 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := family_fourth_bound (show 0 < ε/2 by positivity)
  refine ⟨8*C,by positivity,P₀,hP₀,?_⟩
  intro P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₂ hR hM₁R hM₂R hvolume hsmall
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH₁0 : 0 ≤ H₁ := zero_le_one.trans hH₁
  have hH₂0 : 0 ≤ H₂ := zero_le_one.trans hH₂
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hH : ∀ h ∈ sourceHeights H₁ H₂,
      0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ 4*P ∧ (h.2 : ℝ) ≤ 4*P := by
    intro h hh
    rcases Finset.mem_product.mp hh with ⟨h1,h2⟩
    have hp1 := (Finset.mem_Icc.mp h1).1
    have hp2 := (Finset.mem_Icc.mp h2).1
    have hb1 := (Nat.cast_le.mpr (Finset.mem_Icc.mp h1).2).trans
      (Nat.floor_le (by positivity : 0 ≤ 2*H₁))
    have hb2 := (Nat.cast_le.mpr (Finset.mem_Icc.mp h2).2).trans (Nat.floor_le hH₂0)
    exact ⟨hp1,hp2,by linarith,by linarith⟩
  have hB : ∀ m ∈ sourceCoefficients Q R M₁ M₂,
      0 < m.1 ∧ 0 < m.2 ∧ (m.1 : ℝ) ≤ 4*P ∧ (m.2 : ℝ) ≤ 4*P := by
    intro m hm
    rcases Finset.mem_product.mp hm with ⟨h1,h2⟩
    exact ⟨(mem_smoothNumbers.mp (Finset.mem_filter.mp h1).1).1.1,
      (mem_smoothNumbers.mp (Finset.mem_filter.mp h2).1).1.1,
      ((Finset.mem_filter.mp h1).2.2).trans hM₁R,
      ((Finset.mem_filter.mp h2).2.2).trans hM₂R⟩
  have hBcard := sourceCoefficients_card_le (Q := Q) hR0 hM₁0 hM₂0
  have hb := hbound P hPP (sourceHeights H₁ H₂) (sourceCoefficients Q R M₁ M₂) ⌊4*P⌋₊
    (Nat.floor_le (by positivity)) hH hB (hBcard.trans hvolume)
  have hcard : ((sourceHeights H₁ H₂ ×ˢ sourceCoefficients Q R M₁ M₂).card : ℝ) ≤
      2*H₁*H₂*M₁*M₂*R^2 := by
    rw [Finset.card_product,Nat.cast_mul]
    exact (mul_le_mul (sourceHeights_card_le hH₁0 hH₂0) hBcard
      (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
  have hR6 : R^6 ≤ P^(ε/2) := by
    calc
      _ ≤ (P^(ε/12))^6 := pow_le_pow_left₀ hR0 hsmall 6
      _ = P^(ε/2) := by rw [← Real.rpow_mul_natCast hPpos.le]; congr 1; norm_num; ring
  simp_rw [source_sum_eq_family]
  calc
    _ ≤ C*P^(2+ε/2)*((sourceHeights H₁ H₂ ×ˢ sourceCoefficients Q R M₁ M₂).card : ℝ)^3 := hb
    _ ≤ C*P^(2+ε/2)*(2*H₁*H₂*M₁*M₂*R^2)^3 := by gcongr
    _ = (8*C)*P^(2+ε/2)*H₁^3*H₂^3*M₁^3*M₂^3*R^6 := by ring
    _ ≤ (8*C)*P^(2+ε/2)*H₁^3*H₂^3*M₁^3*M₂^3*P^(ε/2) := by gcongr
    _ = _ := by
      have hp : P^(2+ε/2)*P^(ε/2)=P^(2+ε) := by
        rw [← Real.rpow_add hPpos]
        congr 1
        ring
      calc
        _ = (8*C)*(P^(2+ε/2)*P^(ε/2))*H₁^3*H₂^3*M₁^3*M₂^3 := by ring
        _ = _ := by rw [hp]

/-- The sharp j=2 fourth terminal for degree nine, with all arithmetic and
analytic inputs proved on the actual source domain. -/
theorem source_ninth_second_fourth_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → M₁ ≤ P^(1/9 : ℝ) → 1 ≤ M₂ → M₂ ≤ P^(1/9 : ℝ) →
      1 ≤ R → R ≤ P^(min (ε/12) (1/24 : ℝ)) →
      (∫ α in (0 : ℝ)..1,‖sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α‖^4) ≤
        C*P^(2+ε)*H₁^3*H₂^3*M₁^3*M₂^3 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_fourth_moment_of_volume hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hsmall
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hRpow : R ≤ P^(1/24 : ℝ) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_right _ _))
  have hReps : R ≤ P^(ε/12) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hproduct (M : ℝ) (hM : 0 ≤ M) (hMP : M ≤ P^(1/9 : ℝ)) : M*R ≤ 4*P := by
    calc
      _ ≤ P^(1/9 : ℝ)*P^(1/24 : ℝ) := mul_le_mul hMP hRpow hR0 (Real.rpow_nonneg hPpos.le _)
      _ = P^(11/72 : ℝ) := by rw [← Real.rpow_add hPpos]; norm_num
      _ ≤ P^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _ ≤ 4*P := by rw [Real.rpow_one]; linarith
  have hvolume : M₁*M₂*R^2 ≤ P^(1/3 : ℝ) := by
    calc
      _ ≤ (P^(1/9 : ℝ)*P^(1/9 : ℝ))*(P^(1/24 : ℝ))^2 := by gcongr
      _ = P^(2/9 : ℝ)*P^(1/12 : ℝ) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le]
        norm_num
      _ = P^(11/36 : ℝ) := by rw [← Real.rpow_add hPpos]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  exact hbound P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₂ hR
    (hproduct M₁ hM₁0 hM₁P) (hproduct M₂ hM₂0 hM₂P) hvolume hReps

#print axioms source_ninth_second_fourth_moment
end Waring.SeedCompletionNinthSecondFourthSource
