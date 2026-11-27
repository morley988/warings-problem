import WaringSiegel.WSL4ArchProductMeasure

/-! # Measurable real integration and pruning on actual trace arcs -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceMajorArc_integral_real_measurable_eq_centered
    (H L : ℝ) (hH : 0<H) (hL : 0≤L)
    (hsmall : (2:ℝ)^finrank ℚ K*L^2<
      (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*H^finrank ℚ K)
    (γ : K) (f : ArchimedeanTraceTorus K → ℝ) (hf : Measurable f) :
    (∫ q in traceMajorArc H L γ,f q ∂traceHaar) =
      ∫ β in centeredTraceArc H L γ,
        f (Submodule.Quotient.mk (mixedEmbedding K γ+β))
          ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  have hπ : Measurable (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) :=
    (show Continuous (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
      from continuous_quotient_mk').measurable
  rw [traceMajorArc,traceHaar_restrict_projected_eq_map _
    (productMajorArc_isCompact _ inverseDifferent_ne_zero H L hH γ)
    (quotient_injOn_productMajorArc H L hH hL hsmall γ),
    integral_map hπ.aemeasurable hf.aestronglyMeasurable]
  exact integral_productMajorArc_real_eq_centered H L γ _

local instance pruningProjectionCentersFintype (N : ℕ) :
    Fintype (traceRationalCenters K N) := Fintype.ofFinite _

theorem traceMajorArcUnion_integral_real_measurable_eq_centered_sum
    (H L : ℝ) (hH : 0<H) (hL : 0≤L)
    (hsmall : (2:ℝ)^finrank ℚ K*L^2<
      (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*H^finrank ℚ K)
    (f : ArchimedeanTraceTorus K → ℝ) (hf : Measurable f)
    (hfi : Integrable f traceHaar) :
    (∫ q in traceMajorArcUnion (K := K) H L,f q ∂traceHaar) =
      ∑ q : traceRationalCenters K ⌊L⌋₊,
        ∫ β in centeredTraceArc H L (traceCenterRepresentative q),
          f (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))
            ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  rw [traceMajorArcUnion_eq_finite_union,integral_iUnion_fintype
    (fun q => traceMajorArc_measurableSet H L hH (traceCenterRepresentative q))
    (traceMajorArcUnion_pairwise_disjoint H L hH hL hsmall)
    (fun _ => hfi.integrableOn)]
  apply Finset.sum_congr rfl
  intro q hq
  exact traceMajorArc_integral_real_measurable_eq_centered H L hH hL hsmall
    (traceCenterRepresentative q) f hf

theorem traceMajorArcUnion_pruned_integral_real_eq_centered_sum
    (H L M : ℝ) (hH : 0<H) (hM : 0≤M)
    (hsmall : (2:ℝ)^finrank ℚ K*M^2<
      (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*H^finrank ℚ K)
    (f : ArchimedeanTraceTorus K → ℝ) (hf : Measurable f)
    (hfi : Integrable f traceHaar) :
    (∫ q in traceMajorArcUnion (K := K) H M\traceMajorArcUnion H L,f q ∂traceHaar) =
      ∑ q : traceRationalCenters K ⌊M⌋₊,
        ∫ β in centeredTraceArc H M (traceCenterRepresentative q),
          (traceMajorArcUnion (K := K) H L)ᶜ.indicator f
            (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))
            ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  have hA := (traceMajorArcUnion_measurableSet (K := K) H L hH).compl
  have h := traceMajorArcUnion_integral_real_measurable_eq_centered_sum H M hH hM hsmall
    ((traceMajorArcUnion (K := K) H L)ᶜ.indicator f) (hf.indicator hA) (hfi.indicator hA)
  rw [setIntegral_indicator hA] at h
  simpa only [Set.diff_eq] using h

theorem traceMajorArcUnion_integral_sub_norm_le_norm_integral
    (H L M : ℝ) (hH : 0<H) (hLM : L≤M)
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    ‖(∫ q in traceMajorArcUnion (K := K) H M,f q ∂traceHaar)-
        (∫ q in traceMajorArcUnion H L,f q ∂traceHaar)‖ ≤
      ∫ q in traceMajorArcUnion (K := K) H M\traceMajorArcUnion H L,‖f q‖ ∂traceHaar := by
  have hsub : traceMajorArcUnion (K := K) H L⊆traceMajorArcUnion H M := by
    intro q hq
    obtain ⟨γ,hγ⟩ := Set.mem_iUnion.mp hq
    obtain ⟨x,hx,hxq⟩ := hγ
    exact Set.mem_iUnion.mpr ⟨γ,x,le_trans hx hLM,hxq⟩
  have hfi : Integrable f traceHaar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_diff (traceMajorArcUnion_measurableSet H L hH) hfi.integrableOn hsub]
  exact norm_integral_le_integral_norm _

#print axioms traceMajorArcUnion_pruned_integral_real_eq_centered_sum
#print axioms traceMajorArcUnion_integral_sub_norm_le_norm_integral
end WaringSiegel.WSL4
