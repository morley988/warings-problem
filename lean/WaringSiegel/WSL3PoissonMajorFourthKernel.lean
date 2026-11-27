import WaringSiegel.WSL3IdealPoissonCubicEnlarged
import WaringSiegel.WSL3IdealPoissonMeasure
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi

/-! # Integrable fourth-power stationary kernel with the actual trace-dual scaling -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding WaringSiegel.WSL3
open scoped NumberField Classical BigOperators ENNReal
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def cubicMajorFourthKernel (θ : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, (1+‖θ.1 w‖)^(-2 : ℝ)) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖θ.2 w‖)^(-4 : ℝ)

theorem cubicMajorFourthKernel_nonneg (θ : mixedSpace K) : 0 ≤ cubicMajorFourthKernel θ := by
  unfold cubicMajorFourthKernel
  positivity

theorem cubicMajorFourthKernel_eq (θ : mixedSpace K) :
    cubicMajorFourthKernel θ = 1/(cubicProductStationaryWeight θ)^4 := by
  unfold cubicMajorFourthKernel cubicProductStationaryWeight
  rw [one_div, mul_pow, mul_inv]
  simp only [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), show (2:ℝ)=(2:ℕ) by norm_num,
      Real.rpow_natCast]
    congr 1
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,Real.sq_sqrt (by positivity)]
  · apply Finset.prod_congr rfl
    intro w hw
    rw [Real.rpow_neg (by positivity), show (4:ℝ)=(4:ℕ) by norm_num, Real.rpow_natCast]

theorem cubicMajorFourthKernel_integrable :
    Integrable (cubicMajorFourthKernel (K := K)) := by
  have hr : Integrable (fun x : ℝ => (1+‖x‖)^(-2 : ℝ)) :=
    integrable_one_add_norm (by norm_num : (finrank ℝ ℝ : ℝ) < 2)
  have hc : Integrable (fun x : ℂ => (1+‖x‖)^(-4 : ℝ)) :=
    integrable_one_add_norm (by norm_num [Complex.finrank_real_complex] : (finrank ℝ ℂ : ℝ) < 4)
  have hrr := Integrable.fintype_prod (ι := {w : InfinitePlace K // IsReal w}) (fun _ => hr)
  have hcc := Integrable.fintype_prod (ι := {w : InfinitePlace K // IsComplex w}) (fun _ => hc)
  simpa only [cubicMajorFourthKernel, volume_pi] using hrr.mul_prod hcc

theorem cubicMajorFourthKernel_dual_integrable :
    Integrable (cubicMajorFourthKernel (K := K))
      (archimedeanDualMeasure (integerLatticeSourceScale K)) := by
  exact cubicMajorFourthKernel_integrable.smul_measure ENNReal.ofReal_ne_top

theorem cubicMajorFourthKernel_integral_scale (P : ℝ) (hP : 0 < P) :
    (∫ θ : mixedSpace K, cubicMajorFourthKernel (P^3 • θ)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
    ((P^finrank ℚ K)^3)⁻¹ *
      ∫ θ : mixedSpace K, cubicMajorFourthKernel θ
        ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  have h := Measure.integral_comp_smul_of_nonneg μ cubicMajorFourthKernel (P^3)
    (hR := pow_nonneg hP.le 3)
  simpa only [mixedEmbedding.finrank, smul_eq_mul, ← pow_mul, Nat.mul_comm 3] using h

end WaringSiegel.WSL3Poisson
#print axioms WaringSiegel.WSL3Poisson.cubicMajorFourthKernel_dual_integrable
#print axioms WaringSiegel.WSL3Poisson.cubicMajorFourthKernel_integral_scale
