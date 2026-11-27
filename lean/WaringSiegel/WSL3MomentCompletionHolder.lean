import WaringSiegel.WSL3MomentCompletion
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# The exact L¹ cost of Fourier completion in every integer moment

A finite-measure Jensen inequality gives the exponent n-1 on the Fourier
mass. Applied to an integrable complex amplitude, this preserves the full
remaining oscillatory moment instead of replacing it by a supremum.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_nonneg_pow_le_mass_mul [IsFiniteMeasure μ] (n : ℕ) (f : Ω → ℝ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf : Integrable f μ)
    (hfp : Integrable (fun x => f x^(n+1)) μ) :
    (∫ x, f x ∂μ)^(n+1) ≤ (μ.real Set.univ)^n * ∫ x, f x^(n+1) ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  letI : NeZero μ := ⟨hμ⟩
  have hm : 0 < μ.real Set.univ := measureReal_univ_pos
  have h := (convexOn_pow (𝕜 := ℝ) (n+1)).map_average_le
    (continuous_pow (n+1)).continuousOn isClosed_Ici hf0 hf hfp
  simp only [average_eq, smul_eq_mul] at h
  calc
    (∫ x, f x ∂μ)^(n+1) = (μ.real Set.univ)^(n+1) *
        ((μ.real Set.univ)⁻¹*(∫ x, f x ∂μ))^(n+1) := by
      rw [← mul_pow, mul_inv_cancel_left₀ hm.ne']
    _ ≤ (μ.real Set.univ)^(n+1) * ((μ.real Set.univ)⁻¹ * ∫ x, f x^(n+1) ∂μ) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

theorem weighted_integral_nonneg_pow_le (n : ℕ) (h f : Ω → ℝ)
    (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x) (hh : Integrable h μ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable (fun x => h x*f x) μ)
    (hfpi : Integrable (fun x => h x*f x^(n+1)) μ) :
    (∫ x, h x*f x ∂μ)^(n+1) ≤
      (∫ x, h x ∂μ)^n * ∫ x, h x*f x^(n+1) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (h x))
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hh.2
  have he (g : Ω → ℝ) : (∫ x, g x ∂ν) = ∫ x, h x*g x ∂μ := by
    rw [show ν = μ.withDensity (fun x => ENNReal.ofReal (h x)) from rfl,
      integral_withDensity_eq_integral_toReal_smul hhm.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hh0 _), smul_eq_mul]
  have hmass : ν.real Set.univ = ∫ x, h x ∂μ := by
    simpa only [integral_const, smul_eq_mul, mul_one] using he (fun _ => 1)
  have hνf : Integrable f ν := by
    rw [integrable_withDensity_iff_integrable_smul' hhm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hh0 _), smul_eq_mul] using hfi
  have hνfp : Integrable (fun x => f x^(n+1)) ν := by
    rw [integrable_withDensity_iff_integrable_smul' hhm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hh0 _), smul_eq_mul] using hfpi
  have hj := integral_nonneg_pow_le_mass_mul n f (Filter.Eventually.of_forall hf0) hνf hνfp
  simpa only [he, hmass] using hj

/-- Arbitrary complex amplitudes: completing an (n+1)-st moment costs exactly
its L1 mass to power n. Integrability premises are explicit and elementary. -/
theorem norm_integral_mul_pow_le (n : ℕ) (a g : Ω → ℂ)
    (ha : Integrable a μ) (ham : Measurable a)
    (hag : Integrable (fun x => ‖a x‖*‖g x‖) μ)
    (hagp : Integrable (fun x => ‖a x‖*‖g x‖^(n+1)) μ) :
    ‖∫ x, a x*g x ∂μ‖^(n+1) ≤
      (∫ x, ‖a x‖ ∂μ)^n * ∫ x, ‖a x‖*‖g x‖^(n+1) ∂μ := by
  calc
    _ ≤ (∫ x, ‖a x‖*‖g x‖ ∂μ)^(n+1) := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => a x*g x)
    _ ≤ _ := weighted_integral_nonneg_pow_le n (fun x => ‖a x‖) (fun x => ‖g x‖)
      ham.norm (fun _ => norm_nonneg _) ha.norm (fun _ => norm_nonneg _) hag hagp

#print axioms norm_integral_mul_pow_le

end WaringSiegel.WSL3
