import WaringSiegel.WSL4MajorCubicTail
import WaringSiegel.WSL4ArchProductMeasure

/-! # Exact frequency scaling for the cubic pruning annulus -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def scaledCubicPruningRegion (H q X L C0 : ℝ) : Set (mixedSpace K) :=
  {β | L≤q*productArcWeight H β ∧ q*productArcWeight H β≤C0*X}

theorem scaledCubicPruningRegion_smul (H q X L C0 : ℝ) (hH : 0<H) :
    H • scaledCubicPruningRegion (K := K) H q X L C0 = cubicPruningRegion q X L C0 := by
  ext β
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hH.ne']
  change (L≤q*productArcWeight H (H⁻¹ • β) ∧
    q*productArcWeight H (H⁻¹ • β)≤C0*X) ↔ _
  rw [productArcWeight_scale_eq H hH.le,smul_smul,mul_inv_cancel₀ hH.ne',one_smul]
  rfl

theorem scaledCubicPruningRegion_measurableSet (H q X L C0 : ℝ) :
    MeasurableSet (scaledCubicPruningRegion (K := K) H q X L C0) :=
  ((isClosed_le continuous_const (continuous_const.mul (productArcWeight_continuous H))).inter
    (isClosed_le (continuous_const.mul (productArcWeight_continuous H)) continuous_const)).measurableSet

theorem integral_scaledCubicPruningRegion (H q X Y L C0 : ℝ) (hH : 0<H) :
    (∫ β in scaledCubicPruningRegion (K := K) H q X L C0,
      cubicPruningKernel q X Y (H • β)
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      (H^finrank ℚ K)⁻¹ *
        ∫ β in cubicPruningRegion (K := K) q X L C0,cubicPruningKernel q X Y β
          ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have h := Measure.setIntegral_comp_smul_of_pos μ (cubicPruningKernel q X Y)
    (scaledCubicPruningRegion (K := K) H q X L C0) hH
  simpa only [NumberField.mixedEmbedding.finrank,
    scaledCubicPruningRegion_smul H q X L C0 hH,smul_eq_mul] using h

#print axioms integral_scaledCubicPruningRegion
end WaringSiegel.WSL4
