import WaringSiegel.WSL4ArchProductRegion
import WaringSiegel.WSL4MajorScaling

/-! # Product-kernel integration with the actual trace-dual measure -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ENNReal Pointwise nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem productArcWeight_sublevel_dual_integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a L : ℝ), 0 ≤ a → 1 ≤ L →
      (∫ θ in {θ : mixedSpace K | productArcWeight 1 θ ≤ L}, (productArcWeight 1 θ)^a
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤ C*L^(a+1+ε) := by
  obtain ⟨C,hC,hb⟩ := productArcWeight_sublevel_integral_bound (K:=K) ε hε
  let c : ℝ := (4:ℝ)^nrComplexPlaces K/integerLatticeSourceScale K
  have hc : 0 < c := div_pos (pow_pos (by norm_num) _) integerLatticeSourceScale_pos
  refine ⟨c*C,mul_pos hc hC,fun a L ha hL => ?_⟩
  rw [archimedeanDualMeasure,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal hc.le,smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left (hb a L ha hL) hc.le).trans_eq (by dsimp [c]; ring)

theorem integral_centeredTraceArc_real_scale
    (H L : ℝ) (hH : 0<H) (γ : K) (f : mixedSpace K → ℝ) :
    (∫ β in centeredTraceArc H L γ, f (H • β)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      (H^(finrank ℚ K))⁻¹ *
        ∫ β in centeredTraceArc 1 L γ, f β
          ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have h := Measure.setIntegral_comp_smul_of_pos μ f (centeredTraceArc H L γ) hH
  simpa only [NumberField.mixedEmbedding.finrank,centeredTraceArc_smul H L hH γ,smul_eq_mul] using h

theorem integral_productMajorArc_real_eq_centered
    (H L : ℝ) (γ : K) (f : mixedSpace K → ℝ) :
    (∫ x in productMajorArc (inverseDifferent K) H L γ, f x
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      ∫ β in centeredTraceArc H L γ, f (mixedEmbedding K γ+β)
        ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have hA := (productMajorArc_isClosed (inverseDifferent K) H L γ).measurableSet
  change (∫ x in productMajorArc (inverseDifferent K) H L γ, f x ∂μ) = _
  rw [← integral_indicator hA,
    ← integral_add_left_eq_self (μ := μ)
      ((productMajorArc (inverseDifferent K) H L γ).indicator f) (mixedEmbedding K γ)]
  rw [← integral_indicator (centeredTraceArc_measurableSet H L γ)]
  apply integral_congr_ae
  filter_upwards with β
  by_cases hβ : β ∈ centeredTraceArc H L γ
  · rw [Set.indicator_of_mem hβ,
      Set.indicator_of_mem ((mem_productMajorArc_add_center_iff H L γ β).mpr hβ)]
  · rw [Set.indicator_of_notMem hβ,
      Set.indicator_of_notMem (mt (mem_productMajorArc_add_center_iff H L γ β).mp hβ)]

theorem productMajorArc_weight_integral_scale (H L a : ℝ) (hH : 0 < H) (γ : K) :
    (∫ θ in productMajorArc (inverseDifferent K) H L γ,
      (productArcWeight H (θ-mixedEmbedding K γ))^a
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      (H^finrank ℚ K)⁻¹ *
        ∫ β in productFrequencyRegion (K:=K) (L/((traceConductor γ).absNorm:ℝ)),
          (productArcWeight 1 β)^a
            ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  rw [integral_productMajorArc_real_eq_centered]
  simp only [add_sub_cancel_left,productArcWeight_scale_eq H hH.le]
  rw [integral_centeredTraceArc_real_scale H L hH γ
    (fun β => (productArcWeight 1 β)^a),centeredTraceArc_one_eq]

theorem productMajorArc_positive_weight_integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H L a : ℝ), 0 < H → 0 ≤ a → ∀ γ : K,
      ((traceConductor γ).absNorm:ℝ) ≤ L →
      (∫ θ in productMajorArc (inverseDifferent K) H L γ,
        (productArcWeight H (θ-mixedEmbedding K γ))^a
          ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤
        C*(H^finrank ℚ K)⁻¹*(L/((traceConductor γ).absNorm:ℝ))^(a+1+ε) := by
  obtain ⟨C,hC,hb⟩ := productArcWeight_sublevel_dual_integral_bound (K:=K) ε hε
  refine ⟨C,hC,fun H L a hH ha γ hQL => ?_⟩
  have hQ : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ)
  rw [productMajorArc_weight_integral_scale H L a hH γ]
  exact (mul_le_mul_of_nonneg_left (hb a (L/((traceConductor γ).absNorm:ℝ)) ha
    ((one_le_div hQ).mpr hQL)) (inv_nonneg.mpr (pow_nonneg hH.le _))).trans_eq (by ring)

theorem productMajorArc_negative_weight_integral_bound (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H L : ℝ), 0 < H → ∀ γ : K,
      (∫ θ in productMajorArc (inverseDifferent K) H L γ,
        (productArcWeight H (θ-mixedEmbedding K γ))^(-s)
          ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤ C*(H^finrank ℚ K)⁻¹ := by
  let f : mixedSpace K → ℝ := fun θ => (productArcWeight 1 θ)^(-s)
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  have hfi : Integrable f μ := productArcWeight_neg_rpow_dual_integrable s hs
  have hf0 : ∀ θ, 0 ≤ f θ := fun θ => Real.rpow_nonneg (productArcWeight_pos _ _).le _
  let C := (∫ θ, f θ ∂μ)+1
  have hi0 : 0 ≤ ∫ θ, f θ ∂μ := integral_nonneg hf0
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C,hC,fun H L hH γ => ?_⟩
  rw [productMajorArc_weight_integral_scale H L (-s) hH γ]
  have hh := mul_le_mul_of_nonneg_left (setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)
    (s:=productFrequencyRegion (K:=K) (L/((traceConductor γ).absNorm:ℝ))))
    (inv_nonneg.mpr (pow_nonneg hH.le (finrank ℚ K)))
  apply hh.trans
  dsimp only [C]
  nlinarith [inv_nonneg.mpr (pow_nonneg hH.le (finrank ℚ K))]

#print axioms productMajorArc_weight_integral_scale
#print axioms productMajorArc_positive_weight_integral_bound
#print axioms productMajorArc_negative_weight_integral_bound
end WaringSiegel.WSL4
