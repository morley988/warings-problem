import Waring.HeightMeasurability
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.GCongr

/-!
# Actual integration of finite height-sublevel majorants

This turns a pointwise height decomposition into restricted integral means.
The restricted-mean estimate is a separate source input; the integration,
finite summation and height losses are proved here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Waring.SublevelIntegration

theorem finite_sublevel_integral {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) (H : α → ℝ) (Z : ι → ℝ)
    (w : ι → ℝ≥0∞) (F g : α → ℝ≥0∞)
    (hH : Measurable H) (hg : Measurable g)
    (hmajorant : ∀ᵐ x ∂μ, F x ≤ ∑ j ∈ s, if H x ≤ Z j then w j else 0) :
    (∫⁻ x, F x*g x ∂μ) ≤
      ∑ j ∈ s, w j*(∫⁻ x in {x | H x ≤ Z j}, g x ∂μ) := by
  classical
  let f := fun j => Set.indicator {x | H x ≤ Z j} (fun x => w j*g x)
  have hm (j : ι) : Measurable (f j) :=
    (measurable_const.mul hg).indicator (measurableSet_le hH measurable_const)
  have hpt : ∀ᵐ x ∂μ, F x*g x ≤ ∑ j ∈ s, f j x := by
    filter_upwards [hmajorant] with x hx
    apply (mul_le_mul_right' hx (g x)).trans_eq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : H x ≤ Z j <;> simp [f, hh]
  calc
    _ ≤ ∫⁻ x, ∑ j ∈ s, f j x ∂μ := lintegral_mono_ae hpt
    _ = ∑ j ∈ s, ∫⁻ x, f j x ∂μ := lintegral_finset_sum s (fun j _ => hm j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      rw [lintegral_indicator (measurableSet_le hH measurable_const), lintegral_const_mul _ hg]

theorem inverse_power_dyadic_majorant (T : ℕ) {b θ : ℝ}
    (hθ : 0 ≤ θ) (hb : 1 ≤ b) (hbT : b ≤ (2:ℝ)^T) :
    b^(-θ) ≤ ∑ j ∈ Finset.range (T+1),
      if b ≤ (2:ℝ)^j then (2:ℝ)^θ*((2:ℝ)^j)^(-θ) else 0 := by
  induction T with
  | zero =>
      have heq : b=1 := le_antisymm (by simpa using hbT) hb
      subst b
      simpa using Real.one_le_rpow (by norm_num : (1:ℝ)≤2) hθ
  | succ T ih =>
      rw [Finset.sum_range_succ]
      by_cases hprev : b ≤ (2:ℝ)^T
      · exact (ih hprev).trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
      · have hcross : (2:ℝ)^T ≤ b := (lt_of_not_ge hprev).le
        have hfirst : b^(-θ) ≤ ((2:ℝ)^T)^(-θ) :=
          Real.rpow_le_rpow_of_exponent_nonpos (by positivity) hcross (neg_nonpos.mpr hθ)
        have heq : ((2:ℝ)^T)^(-θ) = (2:ℝ)^θ*((2:ℝ)^(T+1))^(-θ) := by
          rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
          rw [mul_left_comm, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
          simp
        rw [if_pos hbT]
        exact (hfirst.trans_eq heq).trans (le_add_of_nonneg_left
          (Finset.sum_nonneg (fun j hj => by split_ifs <;> positivity)))

theorem height_weight_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (H : α → ℝ) (g : α → ℝ≥0∞) (T : ℕ) {θ : ℝ}
    (hH : Measurable H) (hg : Measurable g) (hθ : 0 ≤ θ)
    (hlower : ∀ᵐ x ∂μ, 1 ≤ H x) (hupper : ∀ᵐ x ∂μ, H x ≤ (2:ℝ)^T) :
    (∫⁻ x, ENNReal.ofReal ((H x)^(-θ))*g x ∂μ) ≤
      ∑ j ∈ Finset.range (T+1),
        ENNReal.ofReal ((2:ℝ)^θ*((2:ℝ)^j)^(-θ))*
          (∫⁻ x in {x | H x ≤ (2:ℝ)^j}, g x ∂μ) := by
  apply finite_sublevel_integral (Finset.range (T+1)) H (fun j => (2:ℝ)^j)
    (fun j => ENNReal.ofReal ((2:ℝ)^θ*((2:ℝ)^j)^(-θ)))
    (fun x => ENNReal.ofReal ((H x)^(-θ))) g hH hg
  filter_upwards [hlower, hupper] with x hxlo hxhi
  have hh := ENNReal.ofReal_le_ofReal (inverse_power_dyadic_majorant T hθ hxlo hxhi)
  convert hh using 1
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  · intro j hj
    split_ifs <;> positivity

theorem dyadic_power_sum_max (T : ℕ) (e : ℝ) :
    (∑ j ∈ Finset.range (T+1), ((2:ℝ)^j)^e) ≤
      (T+1:ℕ)*max 1 (((2:ℝ)^T)^e) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (T+1)) :
      ((2:ℝ)^j)^e ≤ max 1 (((2:ℝ)^T)^e) := by
    by_cases he : 0 ≤ e
    · apply le_trans _ (le_max_right _ _)
      apply Real.rpow_le_rpow (by positivity) _ he
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos
        (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (le_of_not_ge he)).trans (le_max_left _ _)
  calc
    _ ≤ ∑ j ∈ Finset.range (T+1), max 1 (((2:ℝ)^T)^e) := Finset.sum_le_sum hterm
    _ = _ := by simp

/-- Restricted means and a height majorant yield the exact finite dyadic
terminal bound, including the possible logarithmic loss at the critical exponent. -/
theorem restricted_mean_height_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (H : α → ℝ) (g : α → ℝ≥0∞) (T : ℕ) {θ lam : ℝ}
    (hH : Measurable H) (hg : Measurable g) (hθ : 0 ≤ θ)
    (hlower : ∀ᵐ x ∂μ, 1 ≤ H x) (hupper : ∀ᵐ x ∂μ, H x ≤ (2:ℝ)^T)
    (C : ℝ≥0∞)
    (hmeans : ∀ j ∈ Finset.range (T+1),
      (∫⁻ x in {x | H x ≤ (2:ℝ)^j}, g x ∂μ) ≤ C*ENNReal.ofReal (((2:ℝ)^j)^lam)) :
    (∫⁻ x, ENNReal.ofReal ((H x)^(-θ))*g x ∂μ) ≤
      C*ENNReal.ofReal ((2:ℝ)^θ*(T+1:ℕ)*max 1 (((2:ℝ)^T)^(lam-θ))) := by
  have hh := height_weight_integral H g T hH hg hθ hlower hupper
  have hid (j : ℕ) :
      ENNReal.ofReal ((2:ℝ)^θ*((2:ℝ)^j)^(-θ))*(C*ENNReal.ofReal (((2:ℝ)^j)^lam)) =
        C*ENNReal.ofReal ((2:ℝ)^θ*((2:ℝ)^j)^(lam-θ)) := by
    rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [mul_assoc, ← Real.rpow_add (by positivity)]
    congr 2
    ring
  calc
    _ ≤ ∑ j ∈ Finset.range (T+1),
        ENNReal.ofReal ((2:ℝ)^θ*((2:ℝ)^j)^(-θ))*(C*ENNReal.ofReal (((2:ℝ)^j)^lam)) :=
      hh.trans (Finset.sum_le_sum (fun j hj => mul_le_mul_left' (hmeans j hj) _))
    _ = C*ENNReal.ofReal ((2:ℝ)^θ*∑ j ∈ Finset.range (T+1), ((2:ℝ)^j)^(lam-θ)) := by
      simp_rw [hid]
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun j hj => by positivity), ← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_left'
      apply ENNReal.ofReal_le_ofReal
      have hb := mul_le_mul_of_nonneg_left (dyadic_power_sum_max T (lam-θ)) (by positivity : (0:ℝ)≤(2:ℝ)^θ)
      simpa only [mul_assoc] using hb

theorem restricted_mean_majorant_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (H : α → ℝ) (F g : α → ℝ≥0∞) (T : ℕ) {θ lam : ℝ}
    (hH : Measurable H) (hg : Measurable g) (hθ : 0 ≤ θ)
    (hlower : ∀ᵐ x ∂μ, 1 ≤ H x) (hupper : ∀ᵐ x ∂μ, H x ≤ (2:ℝ)^T)
    (A C : ℝ≥0∞)
    (hpoint : ∀ᵐ x ∂μ, F x ≤ A*ENNReal.ofReal ((H x)^(-θ)))
    (hmeans : ∀ j ∈ Finset.range (T+1),
      (∫⁻ x in {x | H x ≤ (2:ℝ)^j}, g x ∂μ) ≤ C*ENNReal.ofReal (((2:ℝ)^j)^lam)) :
    (∫⁻ x, F x*g x ∂μ) ≤
      A*C*ENNReal.ofReal ((2:ℝ)^θ*(T+1:ℕ)*max 1 (((2:ℝ)^T)^(lam-θ))) := by
  have hweight : Measurable (fun x => ENNReal.ofReal ((H x)^(-θ))*g x) :=
    ((hH.pow_const _).ennreal_ofReal).mul hg
  calc
    _ ≤ ∫⁻ x, A*(ENNReal.ofReal ((H x)^(-θ))*g x) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with x hx
      simpa only [mul_assoc] using mul_le_mul_right' hx (g x)
    _ = A*∫⁻ x, ENNReal.ofReal ((H x)^(-θ))*g x ∂μ := lintegral_const_mul _ hweight
    _ ≤ A*(C*ENNReal.ofReal ((2:ℝ)^θ*(T+1:ℕ)*max 1 (((2:ℝ)^T)^(lam-θ)))) :=
      mul_le_mul_left' (restricted_mean_height_integral H g T hH hg hθ hlower hupper C hmeans) A
    _ = _ := by simp only [mul_assoc]

#print axioms finite_sublevel_integral
#print axioms height_weight_integral
#print axioms restricted_mean_majorant_integral

end Waring.SublevelIntegration
