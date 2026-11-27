import WaringSiegel.WSL2MomentKernelAverage
import Mathlib.MeasureTheory.Group.Integral

/-!
# Finite Haar averaging against an invariant factor

The invariance used in the mixed sixth moment is formalized here at the actual
Bochner integral.  Translation averaging preserves the integral against an
invariant factor, and finite-character orthogonality then permits fiberwise
Cauchy under that integral.  Integrability is retained explicitly; no analytic
mean-value estimate is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace WaringSiegel.WSL2

theorem integral_finite_average {T H : Type*} [MeasurableSpace T] [Fintype H]
    (μ : Measure T) (F : H → T → ℝ) (hF : ∀ η, Integrable (F η) μ) :
    (∫ θ, (𝔼 η, F η θ) ∂μ) = 𝔼 η, ∫ θ, F η θ ∂μ := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [integral_div, integral_finset_sum]
  intro η hη
  exact hF η

theorem integrable_finite_average {T H : Type*} [MeasurableSpace T] [Fintype H]
    (μ : Measure T) (F : H → T → ℝ) (hF : ∀ η, Integrable (F η) μ) :
    Integrable (fun θ => 𝔼 η, F η θ) μ := by
  simp only [Fintype.expect_eq_sum_div_card]
  exact (integrable_finset_sum _ (fun η _ => hF η)).div_const _

variable {T H : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]
  [Fintype H] [Nonempty H]

/-- Exact finite translation averaging for a genuine additive Haar measure. -/
theorem integral_finite_translation_average_mul (μ : Measure T) [μ.IsAddRightInvariant]
    (η : H → T) (f g : T → ℝ) (hfg : Integrable (fun θ => f θ*g θ) μ)
    (hg : ∀ h θ, g (θ+η h)=g θ) :
    (∫ θ, (𝔼 h, f (θ+η h))*g θ ∂μ) = ∫ θ, f θ*g θ ∂μ := by
  have htranslate (h : H) : Integrable (fun θ => f (θ+η h)*g θ) μ := by
    simpa only [hg] using hfg.comp_add_right (η h)
  have hintegral (h : H) : (∫ θ, f (θ+η h)*g θ ∂μ) = ∫ θ, f θ*g θ ∂μ := by
    simpa only [hg] using (integral_add_right_eq_self (fun θ => f θ*g θ) (η h) (μ := μ))
  simp_rw [Finset.expect_mul]
  rw [integral_finite_average μ _ htranslate]
  simp only [hintegral, Finset.expect_const, Finset.univ_nonempty]

/-- The finite translation average times the invariant factor is integrable. -/
theorem integrable_finite_translation_average_mul (μ : Measure T) [μ.IsAddRightInvariant]
    (η : H → T) (f g : T → ℝ) (hfg : Integrable (fun θ => f θ*g θ) μ)
    (hg : ∀ h θ, g (θ+η h)=g θ) :
    Integrable (fun θ => (𝔼 h, f (θ+η h))*g θ) μ := by
  simp_rw [Finset.expect_mul]
  apply integrable_finite_average
  intro h
  simpa only [hg] using hfg.comp_add_right (η h)

end WaringSiegel.WSL2
