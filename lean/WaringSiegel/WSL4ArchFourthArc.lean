import WaringSiegel.WSL3PoissonMajorFourthProjection
import WaringSiegel.WSL4ArchFourthKernel

/-! # A genuine projected cubic major arc has the expected fourth-moment mass

This endpoint is for the actual product bump equal one near zero. Its sole unproved arithmetic input is the displayed
bound for the actual finite cubic sum with arbitrary linear trace twist.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ENNReal nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def nearZeroTraceCubicSum (P : ℝ) (hP : P ≠ 0) : ArchimedeanTraceTorus K → ℂ :=
  compactTraceWeylSum 3 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP

theorem nearZeroTraceCubicSum_continuous (P : ℝ) (hP : P ≠ 0) :
    Continuous (nearZeroTraceCubicSum (K := K) P hP) :=
  compactTraceWeylSum_continuous _ _ _ _ _

theorem nearZeroTraceCubicSum_mk (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) :
    nearZeroTraceCubicSum P hP (Submodule.Quotient.mk θ) =
      ∑' x : 𝓞 K, nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3) := by
  simp only [nearZeroTraceCubicSum,compactTraceWeylSum_mk,
    nearZeroSchwartz_apply,Complex.real_smul]

theorem nearZeroTraceCubicSum_single_arc_fourth
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (κ : ℝ), 0 ≤ κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ (P : ℝ) (hP : 0 < P),
      (∫ q in traceMajorArc (P^3) (L*P^finrank ℚ K) γ,
        ‖nearZeroTraceCubicSum P hP.ne' q‖^4 ∂traceHaar) ≤
          C*κ^4*P^finrank ℚ K := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubic_center_major_bound_enlarged (K := K) L hL
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  let D : ℝ := ∫ θ : mixedSpace K, nearZeroMajorFourthKernel θ ∂μ
  have hD : 0 ≤ D := integral_nonneg nearZeroMajorFourthKernel_nonneg
  refine ⟨C^4*(D+1),by positivity,?_⟩
  intro γ κ hκ hfinite P hP
  let W := P^finrank ℚ K
  have hW : 0 < W := pow_pos hP _
  let A := productMajorArc (inverseDifferent K) (P^3) (L*W) γ
  have hA : IsCompact A := productMajorArc_isCompact _ inverseDifferent_ne_zero _ _ (pow_pos hP 3) γ
  let f : ArchimedeanTraceTorus K → ℝ := fun q => ‖nearZeroTraceCubicSum P hP.ne' q‖^4
  have hfc : Continuous f := (nearZeroTraceCubicSum_continuous P hP.ne').norm.pow 4
  have hfn : ∀ q, 0 ≤ f q := fun _ => pow_nonneg (norm_nonneg _) _
  let g : mixedSpace K → ℝ := fun θ => (C*κ*W)^4 *
    nearZeroMajorFourthKernel (P^3 • (θ-mixedEmbedding K γ))
  have hgi : Integrable g μ := by
    have hk : Integrable (nearZeroMajorFourthKernel (K := K)) μ := nearZeroMajorFourthKernel_dual_integrable
    have hs := hk.comp_smul (pow_ne_zero 3 hP.ne')
    exact (hs.comp_sub_right (mixedEmbedding K γ)).const_mul _
  have hgn : ∀ θ, 0 ≤ g θ := fun θ =>
    mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg hC.le hκ) hW.le) _)
      (nearZeroMajorFourthKernel_nonneg _)
  have hbound (θ : mixedSpace K) (hθ : θ ∈ A) : f (Submodule.Quotient.mk θ) ≤ g θ := by
    have hm : (Ideal.absNorm (traceConductor γ) : ℝ) *
        productArcWeight (P^3) (θ-mixedEmbedding K γ) ≤ L*P^finrank ℚ K := hθ
    have hh := hb γ κ hκ hfinite P hP (θ-mixedEmbedding K γ) hm
    have he : mixedEmbedding K γ + (θ-mixedEmbedding K γ) = θ := by abel
    rw [he, ← nearZeroTraceCubicSum_mk P hP.ne'] at hh
    have hp4 := pow_le_pow_left₀ (norm_nonneg _) hh 4
    change ‖nearZeroTraceCubicSum P hP.ne' (Submodule.Quotient.mk θ)‖^4 ≤ _
    simpa only [g,W,nearZeroMajorFourthKernel_eq,div_pow,div_eq_mul_inv,mul_pow,inv_pow,mul_one,one_mul] using hp4
  have hint : (∫ θ, g θ ∂μ) = C^4*κ^4*W*D := by
    rw [show g = fun θ => (C*κ*W)^4 * nearZeroMajorFourthKernel (P^3 • (θ-mixedEmbedding K γ)) from rfl]
    rw [integral_const_mul, integral_sub_right_eq_self
      (fun t : mixedSpace K => nearZeroMajorFourthKernel (P^3 • t)) (mixedEmbedding K γ),
      nearZeroMajorFourthKernel_integral_scale P hP]
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

end WaringSiegel.WSL4
#print axioms WaringSiegel.WSL4.nearZeroTraceCubicSum_single_arc_fourth
