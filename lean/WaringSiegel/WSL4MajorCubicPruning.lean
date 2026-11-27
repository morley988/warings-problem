import WaringSiegel.WSL4MajorCubicScale
import WaringSiegel.WSL4MajorCubicProjection
import WaringSiegel.WSL4MajorCubicCenterMass
import WaringSiegel.WSL4MajorMass

/-! # Actual trace-torus pruning from the eighth-kappa product kernel -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem cubicPruningKernel_nonneg (q X Y : ℝ) (β : mixedSpace K) :
    0≤cubicPruningKernel q X Y β := by
  dsimp [cubicPruningKernel]
  exact mul_nonneg (Real.rpow_nonneg (productArcWeight_pos 1 β).le _)
    (by positivity)

theorem centered_cubic_pruning_integral_le
    (H X Y L C0 T : ℝ) (hH : 0<H) (hT : 0≤T) (γ : K)
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f)
    (hpoint : ∀ β : mixedSpace K,
      ‖f (Submodule.Quotient.mk (mixedEmbedding K γ+β))‖≤
        T*cubicPruningKernel ((traceConductor γ).absNorm:ℝ) X Y (H • β)) :
    (∫ β in centeredTraceArc H (C0*X) γ,
      (traceMajorArcUnion (K := K) H L)ᶜ.indicator (fun q => ‖f q‖)
        (Submodule.Quotient.mk (mixedEmbedding K γ+β))
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤
      T*(H^finrank ℚ K)⁻¹ *
        ∫ β in cubicPruningRegion (K := K) ((traceConductor γ).absNorm:ℝ) X L C0,
          cubicPruningKernel ((traceConductor γ).absNorm:ℝ) X Y β
            ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  let A := centeredTraceArc H (C0*X) γ
  let E := scaledCubicPruningRegion (K := K) H ((traceConductor γ).absNorm:ℝ) X L C0
  let π : mixedSpace K → ArchimedeanTraceTorus K :=
    fun β => Submodule.Quotient.mk (mixedEmbedding K γ+β)
  let g : mixedSpace K → ℝ := fun β =>
    T*cubicPruningKernel ((traceConductor γ).absNorm:ℝ) X Y (H • β)
  have hπ : Continuous π := continuous_quotient_mk'.comp (continuous_const.add continuous_id)
  have hAc : IsCompact A := centeredTraceArc_isCompact H (C0*X) hH γ
  have hE : MeasurableSet E := scaledCubicPruningRegion_measurableSet H _ X L C0
  have hEA : E⊆A := fun β hβ => hβ.2
  have hS := (traceMajorArcUnion_measurableSet (K := K) H L hH).compl
  have hfi : IntegrableOn (fun β =>
      (traceMajorArcUnion (K := K) H L)ᶜ.indicator (fun q => ‖f q‖) (π β)) A μ := by
    have hi := (hf.norm.comp hπ).continuousOn.integrableOn_compact (μ := μ) hAc
    simpa only [Set.indicator_comp_right] using hi.indicator (hS.preimage hπ.measurable)
  have hg : Continuous g := continuous_const.mul
    ((cubicPruningKernel_continuous _ X Y).comp (continuous_const.smul continuous_id))
  have hgi : IntegrableOn (E.indicator g) A μ :=
    (hg.continuousOn.integrableOn_compact hAc).indicator hE
  have hle (β : mixedSpace K) (hβ : β∈A) :
      (traceMajorArcUnion (K := K) H L)ᶜ.indicator (fun q => ‖f q‖) (π β)≤E.indicator g β := by
    by_cases hout : π β∈(traceMajorArcUnion (K := K) H L)ᶜ
    · have hlow : L<((traceConductor γ).absNorm:ℝ)*productArcWeight H β := by
        by_contra hn
        have hmem : π β∈traceMajorArcUnion (K := K) H L := by
          apply Set.mem_iUnion.mpr
          refine ⟨γ,mixedEmbedding K γ+β,?_,rfl⟩
          exact (mem_productMajorArc_add_center_iff H L γ β).mpr (le_of_not_gt hn)
        exact hout hmem
      have hm : β∈E := ⟨hlow.le,hβ⟩
      rw [Set.indicator_of_mem hout,Set.indicator_of_mem hm]
      exact hpoint β
    · rw [Set.indicator_of_notMem hout]
      by_cases hm : β∈E
      · rw [Set.indicator_of_mem hm]
        exact mul_nonneg hT (cubicPruningKernel_nonneg _ _ _ _)
      · rw [Set.indicator_of_notMem hm]
  calc
    _ ≤ ∫ β in A,E.indicator g β ∂μ := setIntegral_mono_on hfi hgi hAc.measurableSet hle
    _ = T*∫ β in E,cubicPruningKernel ((traceConductor γ).absNorm:ℝ) X Y (H • β) ∂μ := by
      rw [setIntegral_indicator hE,Set.inter_eq_right.mpr hEA]
      exact integral_const_mul _ _
    _ = _ := by
      rw [integral_scaledCubicPruningRegion H _ X Y L C0 hH]
      ring

local instance cubicPruningCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

theorem traceMajorArcUnion_kappa_pruning_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v)
    (C0 : ℝ) (hC0 : 1≤C0) :
    ∃ C : ℝ, 0<C ∧ ∀ H X Y L Z : ℝ, 0<H → 0<X → 0≤Y → 0<L → 0≤Z →
      (2:ℝ)^finrank ℚ K*(C0*X)^2<
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*H^finrank ℚ K →
      ∀ f : ArchimedeanTraceTorus K → ℂ, Continuous f →
      (∀ γ : K, ∀ β : mixedSpace K,
        ‖f (Submodule.Quotient.mk (mixedEmbedding K γ+β))‖≤
          Z*cubicKappaIdeal B (traceConductor γ)^8*
            cubicPruningKernel ((traceConductor γ).absNorm:ℝ) X Y (H • β)) →
      (∫ q in traceMajorArcUnion (K := K) H (C0*X)\traceMajorArcUnion H L,‖f q‖ ∂traceHaar) ≤
        C*Z*(H^finrank ℚ K)⁻¹*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by
  obtain ⟨C,hC,hbound⟩ := cubicPruning_kappa_integral_bound B hB C0 hC0
  refine ⟨C,hC,?_⟩
  intro H X Y L Z hH hX hY hL hZ hsmall f hf hpoint
  have hM : 0≤C0*X := mul_nonneg (le_trans zero_le_one hC0) hX.le
  have hfi : Integrable (fun q => ‖f q‖) traceHaar :=
    hf.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [traceMajorArcUnion_pruned_integral_real_eq_centered_sum H L (C0*X)
    hH hM hsmall (fun q => ‖f q‖) hf.norm.measurable hfi]
  calc
    _ ≤ ∑ q : traceRationalCenters K ⌊C0*X⌋₊,
        (Z*cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^8)*
          (H^finrank ℚ K)⁻¹ *
          ∫ β in cubicPruningRegion (K := K)
            ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ) X L C0,
            cubicPruningKernel ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)
              X Y β ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
      apply Finset.sum_le_sum
      intro q hq
      exact centered_cubic_pruning_integral_le H X Y L C0 _ hH (by positivity)
        (traceCenterRepresentative q) f hf (hpoint (traceCenterRepresentative q))
    _ = (Z*(H^finrank ℚ K)⁻¹)*
        ∑ q : traceRationalCenters K ⌊C0*X⌋₊,
          cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^8 *
          ∫ β in cubicPruningRegion (K := K)
            ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ) X L C0,
            cubicPruningKernel ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)
              X Y β ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (Z*(H^finrank ℚ K)⁻¹)*(C*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4))) :=
      mul_le_mul_of_nonneg_left (hbound ⌊C0*X⌋₊ X Y L hX hY hL) (by positivity)
    _ = _ := by ring

#print axioms centered_cubic_pruning_integral_le
#print axioms traceMajorArcUnion_kappa_pruning_bound
end WaringSiegel.WSL4
