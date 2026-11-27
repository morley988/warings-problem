import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual integral inequalities in the two minor-arc endgames

These statements are Hölder inequalities for arbitrary measurable functions
and measures. Taking the measure to be Lebesgue measure restricted to minor
arcs gives the inequalities used in the working manuscript. No exponential
sum estimates are assumed or asserted by the inequalities themselves.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Waring.Holder

theorem three {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hh : AEMeasurable h μ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    (∫⁻ x, f x ^ a * g x ^ b * h x ^ c ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ a * (∫⁻ x, g x ∂μ) ^ b * (∫⁻ x, h x ∂μ) ^ c := by
  let fs : Fin 3 → α → ℝ≥0∞ := ![f, g, h]
  let ws : Fin 3 → ℝ := ![a, b, c]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (fs i) μ := by
    intro i hi
    fin_cases i
    · exact hf
    · exact hg
    · exact hh
  have hw : ∑ i ∈ (Finset.univ : Finset (Fin 3)), ws i = 1 := by
    simpa [ws, Fin.sum_univ_succ, add_assoc] using habc
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ws i := by
    intro i hi
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have H := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ hm hw hn
  simpa [fs, ws, Fin.prod_univ_succ, mul_assoc] using H

/-- Hölder with one ordinary power and two powers of the same smooth factor. -/
theorem mixed {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {m n p a b c : ℝ} (hn : 0 ≤ n) (hp : 0 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    (∫⁻ x, F x ^ (m * a) * g x ^ (n * b + p * c) ∂μ) ≤
      (∫⁻ x, F x ^ m ∂μ) ^ a * (∫⁻ x, g x ^ n ∂μ) ^ b *
        (∫⁻ x, g x ^ p ∂μ) ^ c := by
  have H := three (hF.pow_const m) (hg.pow_const n) (hg.pow_const p) ha hb hc habc
  have hid (x : α) :
      (F x ^ m) ^ a * (g x ^ n) ^ b * (g x ^ p) ^ c =
        F x ^ (m * a) * g x ^ (n * b + p * c) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hn hb) (mul_nonneg hp hc)]
  simpa only [hid] using H

theorem minor8 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, F x ^ (8 : ℕ) * g x ^ (30 : ℕ) ∂μ) ≤
      (∫⁻ x, F x ^ (72 : ℕ) ∂μ) ^ (1 / 9 : ℝ) *
      (∫⁻ x, g x ^ (32 : ℕ) ∂μ) ^ (1 / 9 : ℝ) *
      (∫⁻ x, g x ^ (34 : ℕ) ∂μ) ^ (7 / 9 : ℝ) := by
  have H := mixed hF hg (m := 72) (n := 32) (p := 34)
    (a := 1 / 9) (b := 1 / 9) (c := 7 / 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at H ⊢
  exact H

theorem minor9 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, F x ^ (11 : ℕ) * g x ^ (35 : ℕ) ∂μ) ≤
      (∫⁻ x, F x ^ (90 : ℕ) ∂μ) ^ (11 / 90 : ℝ) *
      (∫⁻ x, g x ^ (38 : ℕ) ∂μ) ^ (5 / 90 : ℝ) *
      (∫⁻ x, g x ^ (40 : ℕ) ∂μ) ^ (74 / 90 : ℝ) := by
  have H := mixed hF hg (m := 90) (n := 38) (p := 40)
    (a := 11 / 90) (b := 5 / 90) (c := 74 / 90)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at H ⊢
  exact H

theorem pruning8 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, F x ^ (8 : ℕ) * g x ^ (30 : ℕ) ∂μ) ≤
      (∫⁻ x, F x ^ (12 : ℕ) ∂μ) ^ (2 / 3 : ℝ) *
      (∫⁻ x, g x ^ (90 : ℕ) ∂μ) ^ (1 / 3 : ℝ) := by
  have H := ENNReal.lintegral_mul_norm_pow_le
    (hF.pow_const (12 : ℝ)) (hg.pow_const (90 : ℝ))
    (p := 2 / 3) (q := 1 / 3) (by norm_num) (by norm_num) (by norm_num)
  have hid (x : α) :
      (F x ^ (12 : ℝ)) ^ (2 / 3 : ℝ) * (g x ^ (90 : ℝ)) ^ (1 / 3 : ℝ) =
        F x ^ (8 : ℕ) * g x ^ (30 : ℕ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [hid] at H
  simpa only [ENNReal.rpow_ofNat] using H

/-- Real integral interpolation, including both endpoint weights. This is the
analytic justification for selecting a two-point chord of moment exponents. -/
theorem integral_pow_interpolation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p p₀ p₁ : ℕ} {t : ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hp : Integrable (fun x => f x ^ p) μ)
    (hp₀ : Integrable (fun x => f x ^ p₀) μ)
    (hp₁ : Integrable (fun x => f x ^ p₁) μ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (horder : (p : ℝ) = (p₀ : ℝ) * t + (p₁ : ℝ) * (1 - t)) :
    (∫ x, f x ^ p ∂μ) ≤
      (∫ x, f x ^ p₀ ∂μ) ^ t * (∫ x, f x ^ p₁ ∂μ) ^ (1 - t) := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hn (r : ℕ) : 0 ≤ᵐ[μ] (fun x => f x ^ r) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (hf x) r)
  have hid (x : α) :
      (f x ^ p₀) ^ t * (f x ^ p₁) ^ (1 - t) = f x ^ p := by
    rw [← Real.rpow_natCast_mul (hf x), ← Real.rpow_natCast_mul (hf x),
      ← Real.rpow_add_of_nonneg (hf x) (mul_nonneg (Nat.cast_nonneg _) ht₀)
        (mul_nonneg (Nat.cast_nonneg _) ht'), ← horder, Real.rpow_natCast]
  have H := ENNReal.lintegral_mul_norm_pow_le
    hp₀.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hp₁.aestronglyMeasurable.aemeasurable.ennreal_ofReal ht₀ ht' (by ring : t + (1-t) = 1)
  have hid' (x : α) :
      ENNReal.ofReal (f x ^ p₀) ^ t * ENNReal.ofReal (f x ^ p₁) ^ (1-t) =
        ENNReal.ofReal (f x ^ p) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hf x) _) ht₀,
      ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hf x) _) ht',
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg (hf x) _) _), hid]
  simp_rw [hid'] at H
  rw [← ofReal_integral_eq_lintegral_ofReal hp (hn p),
    ← ofReal_integral_eq_lintegral_ofReal hp₀ (hn p₀),
    ← ofReal_integral_eq_lintegral_ofReal hp₁ (hn p₁)] at H
  have hi₀ : 0 ≤ ∫ x, f x ^ p₀ ∂μ := integral_nonneg_of_ae (hn p₀)
  have hi₁ : 0 ≤ ∫ x, f x ^ p₁ ∂μ := integral_nonneg_of_ae (hn p₁)
  rw [ENNReal.ofReal_rpow_of_nonneg hi₀ ht₀,
    ENNReal.ofReal_rpow_of_nonneg hi₁ ht',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hi₀ _)] at H
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hi₀ _) (Real.rpow_nonneg hi₁ _))).mp H

end Waring.Holder
