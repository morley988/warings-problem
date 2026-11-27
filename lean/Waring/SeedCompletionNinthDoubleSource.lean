import Waring.SeedCompletionNinthDoubleBox
import Waring.CoefficientPower

/-!
# The literal degree-nine j=2 source second moment

The two smooth coefficient blocks, doubled first shift, and center range
1<=z<=4P are all retained. The explicit smoothness choice absorbs the
block cardinality losses and ensures that their product is at most P.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthDoubleSource
open SeedCompletionNinthDouble SeedCompletionNinthDoubleBox
  CoefficientPower SmoothMoments

def sourceHeights (H₁ H₂ : ℝ) : Finset Pair :=
  Finset.Icc 1 ⌊2*H₁⌋₊ ×ˢ Finset.Icc 1 ⌊H₂⌋₊

def sourceCoefficients (Q R M₁ M₂ : ℝ) : Finset Pair :=
  coefficientBlock Q R M₁ ×ˢ coefficientBlock Q R M₂

def sourceCenters (P : ℝ) : Finset ℕ := Finset.Icc 1 ⌊4*P⌋₊

def sourceNinthSecondSum (P H₁ H₂ Q R M₁ M₂ α : ℝ) : ℂ :=
  actualSum (sourceHeights H₁ H₂) (sourceCoefficients Q R M₁ M₂) (sourceCenters P) α

theorem block_card_le (Q R M : ℝ) (hMR : 0 ≤ M*R) :
    ((coefficientBlock Q R M).card : ℝ) ≤ M*R := by
  calc
    _ ≤ ((smoothNumbers (M*R) R).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (coefficientBlock_subset Q R M)
    _ ≤ (⌊M*R⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le (M*R) R
    _ ≤ M*R := Nat.floor_le hMR

theorem sourceHeights_card_le {H₁ H₂ : ℝ} (h₁ : 0 ≤ H₁) (h₂ : 0 ≤ H₂) :
    ((sourceHeights H₁ H₂).card : ℝ) ≤ 2*H₁*H₂ := by
  simp only [sourceHeights,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul]
  exact mul_le_mul (Nat.floor_le (by positivity : 0 ≤ 2*H₁))
    (Nat.floor_le h₂) (Nat.cast_nonneg _) (by positivity)

theorem sourceCoefficients_card_le {Q R M₁ M₂ : ℝ}
    (hR : 0 ≤ R) (h₁ : 0 ≤ M₁) (h₂ : 0 ≤ M₂) :
    ((sourceCoefficients Q R M₁ M₂).card : ℝ) ≤ M₁*M₂*R^2 := by
  simp only [sourceCoefficients,Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ (M₁*R)*(M₂*R) := mul_le_mul
      (block_card_le Q R M₁ (mul_nonneg h₁ hR))
      (block_card_le Q R M₂ (mul_nonneg h₂ hR)) (Nat.cast_nonneg _) (mul_nonneg h₁ hR)
    _ = _ := by ring

theorem sourceCenters_card_le {P : ℝ} (hP : 0 ≤ P) :
    ((sourceCenters P).card : ℝ) ≤ 4*P := by
  simp only [sourceCenters,Nat.card_Icc,Nat.add_sub_cancel]
  exact Nat.floor_le (by positivity)

/-- The genuine source second moment with the coefficient-volume condition
shown explicitly, before choosing a common smoothness exponent. -/
theorem source_second_moment_of_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ R → M₁*R ≤ 4*P → M₂*R ≤ 4*P →
      M₁*M₂*R^2 ≤ P → R ≤ P^(ε/4) →
      (∫ α in (0 : ℝ)..1, ‖sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α‖^2) ≤
        C*P^(1+ε)*H₁*H₂*M₁*M₂ := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_second_diagonal_size
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
  change (∫ α in (0 : ℝ)..1, ‖sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α‖^2) ≤ _ at hb
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

/-- The published j=2 second-moment shape in degree nine, now proved for
both variable coefficient blocks. No moment, root-count, or divisor-bound
hypothesis remains. The 1/9 parameter ceiling is the source's k=9 range. -/
theorem source_ninth_second_second_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → M₁ ≤ P^(1/9 : ℝ) → 1 ≤ M₂ → M₂ ≤ P^(1/9 : ℝ) →
      1 ≤ R → R ≤ P^(min (ε/4) (7/18 : ℝ)) →
      (∫ α in (0 : ℝ)..1, ‖sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α‖^2) ≤
        C*P^(1+ε)*H₁*H₂*M₁*M₂ := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := source_second_moment_of_volume hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hsmall
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hRpow : R ≤ P^(7/18 : ℝ) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_right _ _))
  have hReps : R ≤ P^(ε/4) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hproduct (M : ℝ) (hM : 0 ≤ M) (hMP : M ≤ P^(1/9 : ℝ)) : M*R ≤ 4*P := by
    calc
      _ ≤ P^(1/9 : ℝ)*P^(7/18 : ℝ) := mul_le_mul hMP hRpow hR0 (Real.rpow_nonneg hPpos.le _)
      _ = P^(1/2 : ℝ) := by rw [← Real.rpow_add hPpos]; norm_num
      _ ≤ P^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _ ≤ 4*P := by rw [Real.rpow_one]; linarith
  have hvolume : M₁*M₂*R^2 ≤ P := by
    calc
      _ ≤ (P^(1/9 : ℝ)*P^(1/9 : ℝ))*(P^(7/18 : ℝ))^2 := by gcongr
      _ = P^(2/9 : ℝ)*P^(7/9 : ℝ) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le]
        norm_num
      _ = P := by rw [← Real.rpow_add hPpos]; norm_num
  exact hbound P hPP₀ H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₂ hR
    (hproduct M₁ hM₁0 hM₁P) (hproduct M₂ hM₂0 hM₂P) hvolume hReps

#print axioms source_second_moment_of_volume
#print axioms source_ninth_second_second_moment
end Waring.SeedCompletionNinthDoubleSource
