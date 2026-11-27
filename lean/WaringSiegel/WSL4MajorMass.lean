import WaringSiegel.WSL4MajorCenteredIntegration

/-! # Summed arc volume and uniform integrated replacement error

The exact projected integral identity makes the sum of the upstairs arc
volumes at most one.  A uniform source error therefore integrates without
an additional conductor-count factor.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem centeredTraceArc_isCompact (H L : ℝ) (hH : 0<H) (γ : K) :
    IsCompact (centeredTraceArc H L γ) := by
  have h := (Homeomorph.addLeft (mixedEmbedding K γ)).isCompact_preimage.mpr
    (productMajorArc_isCompact _ inverseDifferent_ne_zero H L hH γ)
  convert h using 1
  ext β
  exact (mem_productMajorArc_add_center_iff H L γ β).symm

local instance massCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

theorem centeredTraceArc_sum_measure_le_one
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K) :
    (∑ q : traceRationalCenters K ⌊L⌋₊,
      (archimedeanDualMeasure (integerLatticeSourceScale K)).real
        (centeredTraceArc H L (traceCenterRepresentative q))) ≤ 1 := by
  have h := traceMajorArcUnion_integral_eq_centered_sum H L hH hL hsmall
    (fun _ : ArchimedeanTraceTorus K => (1:ℂ)) continuous_const
  have hre := congrArg Complex.re h
  simp only [setIntegral_const,Complex.re_sum,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.one_re,Complex.one_im,Complex.ofReal_im,mul_one,mul_zero,sub_zero] at hre
  rw [← hre]
  exact measureReal_le_one

theorem centeredArcIntegral_error_le
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f)
    (g : traceRationalCenters K ⌊L⌋₊ → mixedSpace K → ℂ)
    (hg : ∀ q, Continuous (g q)) (E : ℝ) (hE : 0≤E)
    (herror : ∀ q, ∀ β ∈ centeredTraceArc H L (traceCenterRepresentative q),
      ‖f (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))-g q β‖≤E) :
    ‖(∫ q in traceMajorArcUnion (K := K) H L, f q ∂traceHaar)-
      ∑ q : traceRationalCenters K ⌊L⌋₊,
        ∫ β in centeredTraceArc H L (traceCenterRepresentative q), g q β
          ∂archimedeanDualMeasure (integerLatticeSourceScale K)‖ ≤ E := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have hi (q : traceRationalCenters K ⌊L⌋₊) :
      IntegrableOn (fun β => f (Submodule.Quotient.mk
        (mixedEmbedding K (traceCenterRepresentative q)+β)))
        (centeredTraceArc H L (traceCenterRepresentative q)) μ := by
    apply ContinuousOn.integrableOn_compact (centeredTraceArc_isCompact H L hH _)
    apply Continuous.continuousOn
    exact hf.comp (continuous_quotient_mk'.comp (continuous_const.add continuous_id))
  have hgi (q : traceRationalCenters K ⌊L⌋₊) :
      IntegrableOn (g q) (centeredTraceArc H L (traceCenterRepresentative q)) μ :=
    (hg q).continuousOn.integrableOn_compact (centeredTraceArc_isCompact H L hH _)
  rw [traceMajorArcUnion_integral_eq_centered_sum H L hH hL hsmall f hf,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q : traceRationalCenters K ⌊L⌋₊,
        ‖(∫ β in centeredTraceArc H L (traceCenterRepresentative q),
          f (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β)) ∂μ)-
        ∫ β in centeredTraceArc H L (traceCenterRepresentative q),g q β ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ q : traceRationalCenters K ⌊L⌋₊,
        E*μ.real (centeredTraceArc H L (traceCenterRepresentative q)) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [← integral_sub (hi q) (hgi q)]
      exact norm_setIntegral_le_of_norm_le_const
        (centeredTraceArc_isCompact H L hH _).measure_lt_top (herror q)
    _ = E * ∑ q : traceRationalCenters K ⌊L⌋₊,
        μ.real (centeredTraceArc H L (traceCenterRepresentative q)) := (Finset.mul_sum _ _ _).symm
    _ ≤ E*1 := mul_le_mul_of_nonneg_left
      (centeredTraceArc_sum_measure_le_one H L hH hL hsmall) hE
    _ = E := mul_one E

#print axioms centeredTraceArc_sum_measure_le_one
#print axioms centeredArcIntegral_error_le
end WaringSiegel.WSL4
