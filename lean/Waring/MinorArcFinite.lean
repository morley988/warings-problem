import Waring.MinorArc

/-!
# Finite constants in the conditional minor-arc estimates

The underlying ENNReal inequalities permit infinite constants. These wrappers
exclude that case and supply an explicit positive real constant, together with
finiteness of the resulting majorant and of the mixed integral. The constants
depend only on the three supplied moment constants, not on the length P.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Waring.MinorArcFinite

def weighted8 (C₀ C₁ C₂ : ℝ≥0∞) : ℝ≥0∞ :=
  C₀ ^ (1/9 : ℝ) * C₁ ^ (1/9 : ℝ) * C₂ ^ (7/9 : ℝ)

def weighted9 (C₀ C₁ C₂ : ℝ≥0∞) : ℝ≥0∞ :=
  C₀ ^ (11/90 : ℝ) * C₁ ^ (5/90 : ℝ) * C₂ ^ (74/90 : ℝ)

def positiveConstant8 (C₀ C₁ C₂ : ℝ≥0∞) : ℝ := (weighted8 C₀ C₁ C₂).toReal + 1
def positiveConstant9 (C₀ C₁ C₂ : ℝ≥0∞) : ℝ := (weighted9 C₀ C₁ C₂).toReal + 1

theorem positiveConstant8_pos (C₀ C₁ C₂ : ℝ≥0∞) :
    0 < positiveConstant8 C₀ C₁ C₂ := by
  exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one

theorem positiveConstant9_pos (C₀ C₁ C₂ : ℝ≥0∞) :
    0 < positiveConstant9 C₀ C₁ C₂ := by
  exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one

theorem weighted8_ne_top {C₀ C₁ C₂ : ℝ≥0∞}
    (h₀ : C₀ ≠ ⊤) (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤) : weighted8 C₀ C₁ C₂ ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₀)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₁))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₂)

theorem weighted9_ne_top {C₀ C₁ C₂ : ℝ≥0∞}
    (h₀ : C₀ ≠ ⊤) (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤) : weighted9 C₀ C₁ C₂ ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₀)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₁))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₂)

theorem le_ofReal_positiveConstant {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    C ≤ ENNReal.ofReal (C.toReal+1) := by
  calc
    C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
    _ ≤ ENNReal.ofReal (C.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)

/-- A finite positive length and finite real coefficient give a finite power majorant. -/
theorem real_majorant_ne_top {P : ℝ≥0∞} (hP₀ : P ≠ 0) (hPtop : P ≠ ⊤)
    (C exponent : ℝ) : ENNReal.ofReal C * P ^ exponent ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero hP₀ hPtop)

theorem degree8 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {P C₀ C₁ C₂ : ℝ≥0∞} (hP : 1 ≤ P) (hPtop : P ≠ ⊤)
    (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 7/200000)
    (h₀ : (∫⁻ x, F x ^ (72 : ℕ) ∂μ) ≤ C₀ * P ^ (63+ε))
    (h₁ : (∫⁻ x, g x ^ (32 : ℕ) ∂μ) ≤ C₁ * P ^ (24+Endgame.delta8_32+ε))
    (h₂ : (∫⁻ x, g x ^ (34 : ℕ) ∂μ) ≤ C₂ * P ^ (26+Endgame.delta8_34+ε)) :
    0 < positiveConstant8 C₀ C₁ C₂ ∧
    (∫⁻ x, F x ^ (8 : ℕ) * g x ^ (30 : ℕ) ∂μ) ≤
      ENNReal.ofReal (positiveConstant8 C₀ C₁ C₂) * P ^ (30-7/200000 : ℝ) ∧
    ENNReal.ofReal (positiveConstant8 C₀ C₁ C₂) * P ^ (30-7/200000 : ℝ) < ⊤ ∧
    (∫⁻ x, F x ^ (8 : ℕ) * g x ^ (30 : ℕ) ∂μ) < ⊤ := by
  have hb := MinorArc.degree8 hF hg hP hPtop hε h₀ h₁ h₂
  have hc := le_ofReal_positiveConstant (weighted8_ne_top hC₀ hC₁ hC₂)
  have hbound : (∫⁻ x, F x ^ (8 : ℕ) * g x ^ (30 : ℕ) ∂μ) ≤
      ENNReal.ofReal (positiveConstant8 C₀ C₁ C₂) * P ^ (30-7/200000 : ℝ) :=
    hb.trans (mul_le_mul_right' hc _)
  have hP₀ : P ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hP)
  have hfinite := (lt_top_iff_ne_top).mpr
    (real_majorant_ne_top hP₀ hPtop (positiveConstant8 C₀ C₁ C₂) (30-7/200000))
  exact ⟨positiveConstant8_pos _ _ _,hbound,hfinite,hbound.trans_lt hfinite⟩

theorem degree9 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {P C₀ C₁ C₂ : ℝ≥0∞} (hP : 1 ≤ P) (hPtop : P ≠ ⊤)
    (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 1/4000)
    (h₀ : (∫⁻ x, F x ^ (90 : ℕ) ∂μ) ≤ C₀ * P ^ (80+ε))
    (h₁ : (∫⁻ x, g x ^ (38 : ℕ) ∂μ) ≤ C₁ * P ^ (29+Endgame.delta9_38+ε))
    (h₂ : (∫⁻ x, g x ^ (40 : ℕ) ∂μ) ≤ C₂ * P ^ (31+Endgame.delta9_40+ε)) :
    0 < positiveConstant9 C₀ C₁ C₂ ∧
    (∫⁻ x, F x ^ (11 : ℕ) * g x ^ (35 : ℕ) ∂μ) ≤
      ENNReal.ofReal (positiveConstant9 C₀ C₁ C₂) * P ^ (37-1/4000 : ℝ) ∧
    ENNReal.ofReal (positiveConstant9 C₀ C₁ C₂) * P ^ (37-1/4000 : ℝ) < ⊤ ∧
    (∫⁻ x, F x ^ (11 : ℕ) * g x ^ (35 : ℕ) ∂μ) < ⊤ := by
  have hb := MinorArc.degree9 hF hg hP hPtop hε h₀ h₁ h₂
  have hc := le_ofReal_positiveConstant (weighted9_ne_top hC₀ hC₁ hC₂)
  have hbound : (∫⁻ x, F x ^ (11 : ℕ) * g x ^ (35 : ℕ) ∂μ) ≤
      ENNReal.ofReal (positiveConstant9 C₀ C₁ C₂) * P ^ (37-1/4000 : ℝ) :=
    hb.trans (mul_le_mul_right' hc _)
  have hP₀ : P ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hP)
  have hfinite := (lt_top_iff_ne_top).mpr
    (real_majorant_ne_top hP₀ hPtop (positiveConstant9 C₀ C₁ C₂) (37-1/4000))
  exact ⟨positiveConstant9_pos _ _ _,hbound,hfinite,hbound.trans_lt hfinite⟩

#print axioms degree8
#print axioms degree9
end Waring.MinorArcFinite
