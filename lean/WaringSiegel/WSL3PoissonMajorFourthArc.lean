import WaringSiegel.WSL3PoissonMajorFourthProjection
import WaringSiegel.WSL3PoissonMajorFourthKernel

/-! # A genuine projected cubic major arc has the expected fourth-moment mass

This endpoint is for the literal fixed smooth root weight, supported away
from zero at every place. Its sole unproved arithmetic input is the displayed
bound for the actual finite cubic sum with arbitrary linear trace twist.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped NumberField Classical BigOperators ENNReal nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def smoothRootComplexWeight (ρ R : ℝ) : mixedSpace K → ℂ := fun x => (smoothRootWeight ρ R x : ℂ)

theorem smoothRootComplexWeight_hasCompactSupport (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    HasCompactSupport (smoothRootComplexWeight (K := K) ρ R) :=
  (smoothRootWeight_hasCompactSupport ρ R hρ hR).comp_left (g := Complex.ofReal) (by simp)

def smoothRootTraceCubicSum (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (P : ℝ) (hP : P ≠ 0) : ArchimedeanTraceTorus K → ℂ :=
  compactTraceWeylSum 3 (smoothRootComplexWeight ρ R)
    (smoothRootComplexWeight_hasCompactSupport ρ R hρ hR) P hP

theorem smoothRootTraceCubicSum_continuous (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (P : ℝ) (hP : P ≠ 0) : Continuous (smoothRootTraceCubicSum (K := K) ρ R hρ hR P hP) :=
  compactTraceWeylSum_continuous _ _ _ _ _

theorem smoothRootTraceCubicSum_mk (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) :
    smoothRootTraceCubicSum ρ R hρ hR P hP (Submodule.Quotient.mk θ) =
      ∑' x : 𝓞 K, smoothRootWeight ρ R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3) := by
  simp only [smoothRootTraceCubicSum,compactTraceWeylSum_mk,
    smoothRootComplexWeight,Complex.real_smul]

theorem smoothRootTraceCubicSum_single_arc_fourth
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (κ : ℝ), 0 ≤ κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ (P : ℝ) (hP : 0 < P),
      (∫ q in traceMajorArc (P^3) (L*P^finrank ℚ K) γ,
        ‖smoothRootTraceCubicSum ρ R hρ hR P hP.ne' q‖^4 ∂traceHaar) ≤
          C*κ^4*P^finrank ℚ K := by
  obtain ⟨C,hC,hb⟩ := smoothCubic_center_major_bound_enlarged (K := K) ρ R hρ hR L hL
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  let D : ℝ := ∫ θ : mixedSpace K, cubicMajorFourthKernel θ ∂μ
  have hD : 0 ≤ D := integral_nonneg cubicMajorFourthKernel_nonneg
  refine ⟨C^4*(D+1),by positivity,?_⟩
  intro γ κ hκ hfinite P hP
  let W := P^finrank ℚ K
  have hW : 0 < W := pow_pos hP _
  let A := productMajorArc (inverseDifferent K) (P^3) (L*W) γ
  have hA : IsCompact A := productMajorArc_isCompact _ inverseDifferent_ne_zero _ _ (pow_pos hP 3) γ
  let f : ArchimedeanTraceTorus K → ℝ := fun q => ‖smoothRootTraceCubicSum ρ R hρ hR P hP.ne' q‖^4
  have hfc : Continuous f := (smoothRootTraceCubicSum_continuous ρ R hρ hR P hP.ne').norm.pow 4
  have hfn : ∀ q, 0 ≤ f q := fun _ => pow_nonneg (norm_nonneg _) _
  let g : mixedSpace K → ℝ := fun θ => (C*κ*W)^4 *
    cubicMajorFourthKernel (P^3 • (θ-mixedEmbedding K γ))
  have hgi : Integrable g μ := by
    have hk : Integrable (cubicMajorFourthKernel (K := K)) μ := cubicMajorFourthKernel_dual_integrable
    have hs := hk.comp_smul (pow_ne_zero 3 hP.ne')
    exact (hs.comp_sub_right (mixedEmbedding K γ)).const_mul _
  have hgn : ∀ θ, 0 ≤ g θ := fun θ =>
    mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg hC.le hκ) hW.le) _)
      (cubicMajorFourthKernel_nonneg _)
  have hbound (θ : mixedSpace K) (hθ : θ ∈ A) : f (Submodule.Quotient.mk θ) ≤ g θ := by
    have hm : (Ideal.absNorm (traceConductor γ) : ℝ) *
        productArcWeight (P^3) (θ-mixedEmbedding K γ) ≤ L*P^finrank ℚ K := hθ
    have hh := hb γ κ hκ hfinite P hP (θ-mixedEmbedding K γ) hm
    have he : mixedEmbedding K γ + (θ-mixedEmbedding K γ) = θ := by abel
    rw [he, ← smoothRootTraceCubicSum_mk ρ R hρ hR P hP.ne'] at hh
    have hp4 := pow_le_pow_left₀ (norm_nonneg _) hh 4
    change ‖smoothRootTraceCubicSum ρ R hρ hR P hP.ne' (Submodule.Quotient.mk θ)‖^4 ≤ _
    simpa only [g,W,cubicMajorFourthKernel_eq,div_pow,div_eq_mul_inv,mul_pow,inv_pow,mul_one,one_mul] using hp4
  have hint : (∫ θ, g θ ∂μ) = C^4*κ^4*W*D := by
    rw [show g = fun θ => (C*κ*W)^4 * cubicMajorFourthKernel (P^3 • (θ-mixedEmbedding K γ)) from rfl]
    rw [integral_const_mul, integral_sub_right_eq_self
      (fun t : mixedSpace K => cubicMajorFourthKernel (P^3 • t)) (mixedEmbedding K γ),
      cubicMajorFourthKernel_integral_scale P hP]
    change (C*κ*W)^4 * ((W^3)⁻¹ * D) = C^4*κ^4*W*D
    field_simp [hW.ne']
    <;> ring
  have hproj := traceHaar_integral_projected_le A hA f hfc hfn
  calc
    _ ≤ ∫ θ in A, f (Submodule.Quotient.mk θ) ∂μ := hproj
    _ ≤ ∫ θ in A, g θ ∂μ := setIntegral_mono_on
      ((hfc.comp continuous_quotient_mk').continuousOn.integrableOn_compact hA)
      hgi.integrableOn hA.measurableSet hbound
    _ ≤ ∫ θ, g θ ∂μ := setIntegral_le_integral hgi (Filter.Eventually.of_forall hgn)
    _ = C^4*κ^4*W*D := hint
    _ ≤ (C^4*(D+1))*κ^4*W := by
      nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hC.le 4) (pow_nonneg hκ 4)) hW.le]

end WaringSiegel.WSL3Poisson
#print axioms WaringSiegel.WSL3Poisson.smoothRootTraceCubicSum_single_arc_fourth
