import Waring.Holder
import Waring.Endgame
import Mathlib.Tactic.Linarith

/-!
# Conditional minor-arc bounds for actual integrals

The only number-theoretic premises of these statements are the explicitly
displayed moment inequalities. Hölder and all exponent/small-epsilon arithmetic
are proved here. The measure may be Lebesgue measure restricted to minor arcs.
No Waring conclusion or admissibility predicate is an assumption.
-/

open MeasureTheory
open scoped ENNReal

namespace Waring.MinorArc

theorem weighted_power_product (P C₀ C₁ C₂ : ℝ≥0∞)
    {e₀ e₁ e₂ a b c : ℝ} (hP₀ : P ≠ 0) (hPtop : P ≠ ⊤)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (C₀ * P ^ e₀) ^ a * (C₁ * P ^ e₁) ^ b * (C₂ * P ^ e₂) ^ c =
      (C₀ ^ a * C₁ ^ b * C₂ ^ c) * P ^ (e₀ * a + e₁ * b + e₂ * c) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.mul_rpow_of_nonneg _ _ hb,
    ENNReal.mul_rpow_of_nonneg _ _ hc,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ENNReal.rpow_add _ _ hP₀ hPtop, ENNReal.rpow_add _ _ hP₀ hPtop]
  ac_rfl

theorem three_moment_bounds {A₀ A₁ A₂ P C₀ C₁ C₂ : ℝ≥0∞}
    {e₀ e₁ e₂ a b c : ℝ} (hP₀ : P ≠ 0) (hPtop : P ≠ ⊤)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h₀ : A₀ ≤ C₀ * P ^ e₀) (h₁ : A₁ ≤ C₁ * P ^ e₁)
    (h₂ : A₂ ≤ C₂ * P ^ e₂) :
    A₀ ^ a * A₁ ^ b * A₂ ^ c ≤
      (C₀ ^ a * C₁ ^ b * C₂ ^ c) * P ^ (e₀ * a + e₁ * b + e₂ * c) := by
  calc
    A₀ ^ a * A₁ ^ b * A₂ ^ c ≤
        (C₀ * P ^ e₀) ^ a * (C₁ * P ^ e₁) ^ b * (C₂ * P ^ e₂) ^ c :=
      mul_le_mul' (mul_le_mul' (ENNReal.rpow_le_rpow h₀ ha)
        (ENNReal.rpow_le_rpow h₁ hb)) (ENNReal.rpow_le_rpow h₂ hc)
    _ = _ := weighted_power_product _ _ _ _ hP₀ hPtop ha hb hc

theorem degree8 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {P C₀ C₁ C₂ : ℝ≥0∞} (hP : 1 ≤ P) (hPtop : P ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 7 / 200000)
    (h₀ : (∫⁻ x, F x ^ (72 : ℕ) ∂μ) ≤ C₀ * P ^ (63 + ε))
    (h₁ : (∫⁻ x, g x ^ (32 : ℕ) ∂μ) ≤ C₁ * P ^ (24 + Endgame.delta8_32 + ε))
    (h₂ : (∫⁻ x, g x ^ (34 : ℕ) ∂μ) ≤ C₂ * P ^ (26 + Endgame.delta8_34 + ε)) :
    (∫⁻ x, F x ^ (8 : ℕ) * g x ^ (30 : ℕ) ∂μ) ≤
      (C₀ ^ (1 / 9 : ℝ) * C₁ ^ (1 / 9 : ℝ) * C₂ ^ (7 / 9 : ℝ)) *
        P ^ (30 - 7 / 200000 : ℝ) := by
  have hP₀ : P ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hP)
  have h := three_moment_bounds hP₀ hPtop
    (a := (1/9 : ℝ)) (b := (1/9 : ℝ)) (c := (7/9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) h₀ h₁ h₂
  have he : (63 + ε) * (1/9) + (24 + Endgame.delta8_32 + ε) * (1/9) +
      (26 + Endgame.delta8_34 + ε) * (7/9) =
        Endgame.minorExponent8 Endgame.delta8_32 Endgame.delta8_34 + ε := by
    unfold Endgame.minorExponent8
    ring
  rw [he] at h
  exact (Holder.minor8 hF hg).trans (h.trans
    (mul_le_mul_left' (ENNReal.rpow_le_rpow_of_exponent_le hP
      (Endgame.minor8_epsilon_budget hε)) _))

theorem degree9 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {P C₀ C₁ C₂ : ℝ≥0∞} (hP : 1 ≤ P) (hPtop : P ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 1 / 4000)
    (h₀ : (∫⁻ x, F x ^ (90 : ℕ) ∂μ) ≤ C₀ * P ^ (80 + ε))
    (h₁ : (∫⁻ x, g x ^ (38 : ℕ) ∂μ) ≤ C₁ * P ^ (29 + Endgame.delta9_38 + ε))
    (h₂ : (∫⁻ x, g x ^ (40 : ℕ) ∂μ) ≤ C₂ * P ^ (31 + Endgame.delta9_40 + ε)) :
    (∫⁻ x, F x ^ (11 : ℕ) * g x ^ (35 : ℕ) ∂μ) ≤
      (C₀ ^ (11 / 90 : ℝ) * C₁ ^ (5 / 90 : ℝ) * C₂ ^ (74 / 90 : ℝ)) *
        P ^ (37 - 1 / 4000 : ℝ) := by
  have hP₀ : P ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hP)
  have h := three_moment_bounds hP₀ hPtop
    (a := (11/90 : ℝ)) (b := (5/90 : ℝ)) (c := (74/90 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) h₀ h₁ h₂
  have he : (80 + ε) * (11/90) + (29 + Endgame.delta9_38 + ε) * (5/90) +
      (31 + Endgame.delta9_40 + ε) * (74/90) =
        Endgame.minorExponent9 Endgame.delta9_38 Endgame.delta9_40 + ε := by
    unfold Endgame.minorExponent9
    ring
  rw [he] at h
  exact (Holder.minor9 hF hg).trans (h.trans
    (mul_le_mul_left' (ENNReal.rpow_le_rpow_of_exponent_le hP
      (Endgame.minor9_epsilon_budget hε).le) _))

end Waring.MinorArc
