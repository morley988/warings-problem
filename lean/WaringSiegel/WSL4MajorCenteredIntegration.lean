import WaringSiegel.WSL4MajorArcIntegration

/-! # Centered exact integrals on actual major arcs -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def centeredTraceArc (H L : ℝ) (γ : K) : Set (mixedSpace K) :=
  {β | ((traceConductor γ).absNorm : ℝ) * productArcWeight H β ≤ L}

theorem centeredTraceArc_measurableSet (H L : ℝ) (γ : K) :
    MeasurableSet (centeredTraceArc H L γ) :=
  (isClosed_le (continuous_const.mul (productArcWeight_continuous H))
    continuous_const).measurableSet

theorem mem_productMajorArc_add_center_iff (H L : ℝ) (γ : K) (β : mixedSpace K) :
    mixedEmbedding K γ + β ∈ productMajorArc (inverseDifferent K) H L γ ↔
      β ∈ centeredTraceArc H L γ := by
  simp only [productMajorArc, centeredTraceArc, Set.mem_setOf_eq, add_sub_cancel_left,
    traceConductor]

theorem integral_productMajorArc_eq_centered
    (H L : ℝ) (γ : K) (f : mixedSpace K → ℂ) :
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

theorem traceMajorArc_integral_eq_centered
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (γ : K) (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    (∫ q in traceMajorArc H L γ, f q ∂traceHaar) =
      ∫ β in centeredTraceArc H L γ, f (Submodule.Quotient.mk (mixedEmbedding K γ+β))
        ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  rw [traceMajorArc_integral_eq H L hH hL hsmall γ f hf]
  exact integral_productMajorArc_eq_centered H L γ _

local instance centeredCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

theorem traceMajorArcUnion_integral_eq_centered_sum
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    (∫ q in traceMajorArcUnion (K := K) H L, f q ∂traceHaar) =
      ∑ q : traceRationalCenters K ⌊L⌋₊,
        ∫ β in centeredTraceArc H L (traceCenterRepresentative q),
          f (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))
          ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  rw [traceMajorArcUnion_integral_eq_sum H L hH hL hsmall f hf]
  apply Finset.sum_congr rfl
  intro q hq
  exact integral_productMajorArc_eq_centered H L (traceCenterRepresentative q) _

#print axioms traceMajorArcUnion_integral_eq_centered_sum
end WaringSiegel.WSL4
