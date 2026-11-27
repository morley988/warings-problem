import WaringSiegel.WSL4ArchMajor
import WaringSiegel.WSL3IdealPoissonMeasure
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi

/-! # Integrable fourth-power stationary kernel with the actual trace-dual scaling -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def nearZeroMajorFourthKernel (θ : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, (1+‖θ.1 w‖)^(-(4/3) : ℝ)) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖θ.2 w‖)^(-(8/3) : ℝ)

theorem nearZeroMajorFourthKernel_nonneg (θ : mixedSpace K) : 0 ≤ nearZeroMajorFourthKernel θ := by
  unfold nearZeroMajorFourthKernel
  positivity

theorem nearZeroMajorFourthKernel_eq (θ : mixedSpace K) :
    nearZeroMajorFourthKernel θ = 1/(cubicProductFrequencyWeight (1/3) θ)^4 := by
  unfold nearZeroMajorFourthKernel cubicProductFrequencyWeight
  rw [one_div, mul_pow, mul_inv]
  simp only [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    norm_num
  · apply Finset.prod_congr rfl
    intro w hw
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    norm_num

theorem nearZeroMajorFourthKernel_integrable :
    Integrable (nearZeroMajorFourthKernel (K := K)) := by
  have hr : Integrable (fun x : ℝ => (1+‖x‖)^(-(4/3) : ℝ)) :=
    integrable_one_add_norm (by norm_num : (finrank ℝ ℝ : ℝ) < 4/3)
  have hc : Integrable (fun x : ℂ => (1+‖x‖)^(-(8/3) : ℝ)) :=
    integrable_one_add_norm (by norm_num [Complex.finrank_real_complex] : (finrank ℝ ℂ : ℝ) < 8/3)
  have hrr := Integrable.fintype_prod (ι := {w : InfinitePlace K // IsReal w}) (fun _ => hr)
  have hcc := Integrable.fintype_prod (ι := {w : InfinitePlace K // IsComplex w}) (fun _ => hc)
  simpa only [nearZeroMajorFourthKernel, volume_pi] using hrr.mul_prod hcc

theorem nearZeroMajorFourthKernel_dual_integrable :
    Integrable (nearZeroMajorFourthKernel (K := K))
      (archimedeanDualMeasure (integerLatticeSourceScale K)) := by
  exact nearZeroMajorFourthKernel_integrable.smul_measure ENNReal.ofReal_ne_top

theorem nearZeroMajorFourthKernel_integral_scale (P : ℝ) (hP : 0 < P) :
    (∫ θ : mixedSpace K, nearZeroMajorFourthKernel (P^3 • θ)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
    ((P^finrank ℚ K)^3)⁻¹ *
      ∫ θ : mixedSpace K, nearZeroMajorFourthKernel θ
        ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have h := Measure.integral_comp_smul_of_nonneg μ nearZeroMajorFourthKernel (P^3)
    (hR := pow_nonneg hP.le 3)
  simpa only [mixedEmbedding.finrank, smul_eq_mul, ← pow_mul, Nat.mul_comm 3] using h

end WaringSiegel.WSL4
#print axioms WaringSiegel.WSL4.nearZeroMajorFourthKernel_dual_integrable
#print axioms WaringSiegel.WSL4.nearZeroMajorFourthKernel_integral_scale
