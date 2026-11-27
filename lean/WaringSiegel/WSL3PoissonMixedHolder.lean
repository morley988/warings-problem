import WaringSiegel.WSL3PoissonMixedTorus

/-! # Exact Cauchy--Schwarz/Hölder inequalities for the mixed trace integrals -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped BigOperators
namespace WaringSiegel.WSL3Poisson

section Compact
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Cauchy--Schwarz in a form without square roots. -/
theorem compact_integral_cauchy_sq {f g : Ω → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, g x^2 ∂μ) := by
  have hpq : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hfp : MemLp f (ENNReal.ofReal 2) μ := hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgp : MemLp g (ENNReal.ofReal 2) μ := hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hfp hgp
  have hb' : (∫ x, f x*g x ∂μ) ≤
      Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ) := by
    simpa only [Real.rpow_ofNat,← Real.sqrt_eq_rpow] using hb
  have hfg : 0 ≤ ∫ x, f x*g x ∂μ := integral_nonneg (fun x => mul_nonneg (hf0 x) (hg0 x))
  have hf2 : 0 ≤ ∫ x, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hg2 : 0 ≤ ∫ x, g x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  calc
    _ ≤ (Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ))^2 :=
      pow_le_pow_left₀ hfg hb' 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hf2,Real.sq_sqrt hg2]

/-- Hölder with exponents 4,2,4, expressed as an exact fourth-power bound. -/
theorem compact_integral_holder_424 {f g : Ω → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, f x*g x^4 ∂μ)^4 ≤
      (∫ x, f x^4 ∂μ)*(∫ x, g x^8 ∂μ)*(∫ x, g x^4 ∂μ)^2 := by
  have h1 := compact_integral_cauchy_sq (μ:=μ) (hf.mul (hg.pow 2)) (hg.pow 2)
    (fun x => mul_nonneg (hf0 x) (sq_nonneg _)) (fun x => sq_nonneg _)
  have he1 : (fun x => (f x*g x^2)*g x^2) = (fun x => f x*g x^4) := by funext x; ring
  simp only [he1,mul_pow,← pow_mul] at h1
  have h2 := compact_integral_cauchy_sq (μ:=μ) (hf.pow 2) (hg.pow 4)
    (fun x => sq_nonneg _) (fun x => pow_nonneg (hg0 x) _)
  simp only [← pow_mul] at h2
  have h3 := pow_le_pow_left₀ (sq_nonneg (∫ x, f x*g x^4 ∂μ)) h1 2
  norm_num only [← pow_mul] at h1 h2 h3
  rw [mul_pow] at h3
  apply h3.trans
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

end Compact
end WaringSiegel.WSL3Poisson
