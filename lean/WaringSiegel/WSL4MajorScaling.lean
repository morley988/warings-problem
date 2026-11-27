import WaringSiegel.WSL4MajorCenteredIntegration
import WaringSiegel.WSL4MajorSources

/-! # Exact frequency scaling in the major main term -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem productArcWeight_scale_eq (H : ℝ) (hH : 0≤H) (β : mixedSpace K) :
    productArcWeight H β = productArcWeight 1 (H • β) := by
  simp only [productArcWeight,normAtPlace_smul,abs_of_nonneg hH,one_mul]

theorem centeredTraceArc_smul (H L : ℝ) (hH : 0<H) (γ : K) :
    H • centeredTraceArc H L γ = centeredTraceArc 1 L γ := by
  ext β
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hH.ne']
  change ((traceConductor γ).absNorm:ℝ)*productArcWeight H (H⁻¹ • β)≤L ↔ _
  rw [productArcWeight_scale_eq H hH.le,smul_smul,mul_inv_cancel₀ hH.ne',one_smul]
  rfl

theorem integral_centeredTraceArc_scale
    (H L : ℝ) (hH : 0<H) (γ : K) (f : mixedSpace K → ℂ) :
    (∫ β in centeredTraceArc H L γ, f (H • β)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      (H^(finrank ℚ K))⁻¹ •
        ∫ β in centeredTraceArc 1 L γ, f β
          ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have h := Measure.setIntegral_comp_smul_of_pos μ f (centeredTraceArc H L γ) hH
  simpa only [NumberField.mixedEmbedding.finrank,centeredTraceArc_smul H L hH γ] using h

def productFrequencyRegion (Q : ℝ) : Set (mixedSpace K) :=
  {β | productArcWeight 1 β ≤ Q}

theorem centeredTraceArc_one_eq (L : ℝ) (γ : K) :
    centeredTraceArc 1 L γ = productFrequencyRegion (L/((traceConductor γ).absNorm:ℝ)) := by
  have hN : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ)
  ext β
  change ((traceConductor γ).absNorm:ℝ)*productArcWeight 1 β ≤ L ↔
    productArcWeight 1 β ≤ L/((traceConductor γ).absNorm:ℝ)
  rw [le_div_iff₀ hN,mul_comm]

def productSingularIntegral (k n : ℕ) (ρ R Q : ℝ) (b : mixedSpace K) : ℂ :=
  ∫ β in productFrequencyRegion Q,
    archimedeanTraceCharacter (-β) b *
      pairedWeightedRootIntegral (integerLatticeSourceScale K) k (smoothRootWeight ρ R) β ^ n
    ∂archimedeanDualMeasure (integerLatticeSourceScale K)

def majorScale (k n : ℕ) (P : ℝ) : ℝ := (P^(finrank ℚ K) : ℝ)^((n:ℝ)-k)

theorem majorScale_eq_div (k n : ℕ) (P : ℝ) (hP : 0<P) :
    majorScale (K := K) k n P = P^(finrank ℚ K*n)/(P^k)^(finrank ℚ K) := by
  rw [majorScale,Real.rpow_sub (pow_pos hP _),Real.rpow_natCast,Real.rpow_natCast]
  simp only [← pow_mul,Nat.mul_comm]

theorem smoothPowerCenterMainTerm_integral
    (k n : ℕ) (hk : 0<k) (ρ R L : ℝ) (target : 𝓞 K) (htarget : target≠0) (γ : K) :
    (∫ β in centeredTraceArc ((rootScale k target)^k) L γ,
      smoothPowerCenterMainTerm k ρ R (rootScale k target) γ β ^ n *
        traceTorusCharacter (-target) (Submodule.Quotient.mk (mixedEmbedding K γ+β))
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      (majorScale (K := K) k n (rootScale k target) : ℂ) * majorCompleteCoefficient k n target γ *
        productSingularIntegral k n ρ R (L/((traceConductor γ).absNorm:ℝ))
          (normalizedTarget k 1 target) := by
  have hP := rootScale_pos htarget k
  simp_rw [smoothPowerCenterMainTerm_pow_phase k n hk ρ R target htarget γ]
  rw [integral_const_mul]
  rw [integral_centeredTraceArc_scale ((rootScale k target)^k) L (pow_pos hP k) γ
    (fun β => archimedeanTraceCharacter (-β) (normalizedTarget k 1 target) *
      pairedWeightedRootIntegral (integerLatticeSourceScale K) k (smoothRootWeight ρ R) β^n),
    centeredTraceArc_one_eq,majorScale_eq_div (K := K) k n _ hP]
  simp only [Complex.real_smul,productSingularIntegral]
  push_cast
  simp only [div_eq_mul_inv]
  ring

#print axioms integral_centeredTraceArc_scale
#print axioms smoothPowerCenterMainTerm_integral
end WaringSiegel.WSL4
