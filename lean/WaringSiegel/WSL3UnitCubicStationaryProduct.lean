import WaringSiegel.WSL3UnitComplexStationary
import WaringSiegel.WSL3UnitRealWeightedStationary

/-!
# Actual product-place stationary decay with arbitrary linear twists

At a real place the exponent is one half; at a complex place it is one.
The same estimates retain arbitrary rapid decay in every nonstationary
linear-frequency direction, simultaneously over any subset of places.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

theorem realPlaceCubicIntegral_stationary_tail_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      (Real.sqrt (1+|theta|)*cubicTailWeight (2*R) n |theta| |u|)*
        ‖realPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨Cs,hCs,hs⟩ := realPlaceCubicIntegral_stationary_bound rho R hrho hR
  obtain ⟨Ct,hCt,ht⟩ := realPlaceCubicIntegral_weighted_bound rho R hrho hR (n+1)
  refine ⟨Cs+Ct,by positivity,fun theta u => ?_⟩
  by_cases hreg : cubicTailThreshold (2*R)*(1+|theta|) ≤ |u|
  · have hB := cubicTailThreshold_ge_one (2*R)
    have htu : |theta| ≤ |u| := by nlinarith [abs_nonneg theta]
    have hsq : Real.sqrt (1+|theta|) ≤ 1+|u| := by
      have he := Real.sq_sqrt (by positivity : 0 ≤ 1+|theta|)
      nlinarith [Real.sqrt_nonneg (1+|theta|),abs_nonneg u]
    have hb := ht theta u
    simp only [cubicTailWeight,if_pos hreg,pow_succ] at hb ⊢
    have hm := mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1+|u|) n)
        (norm_nonneg (realPlaceCubicIntegral rho R theta u)))
    nlinarith
  · simp only [cubicTailWeight,if_neg hreg,mul_one]
    have hb := hs theta u
    linarith

theorem complexPlaceCubicIntegral_stationary_tail_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      ((1+‖theta‖)*cubicTailWeight (2*R) n ‖theta‖ ‖u‖)*
        ‖complexPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨Cs,hCs,hs⟩ := complexPlaceCubicIntegral_stationary_bound rho R hrho hR
  obtain ⟨Ct,hCt,ht⟩ := complexPlaceCubicIntegral_weighted_bound rho R hrho hR (n+1)
  refine ⟨Cs+Ct,by positivity,fun theta u => ?_⟩
  by_cases hreg : cubicTailThreshold (2*R)*(1+‖theta‖) ≤ ‖u‖
  · have hB := cubicTailThreshold_ge_one (2*R)
    have htu : 1+‖theta‖ ≤ 1+‖u‖ := by nlinarith [norm_nonneg theta]
    have hb := ht theta u
    simp only [cubicTailWeight,if_pos hreg,pow_succ] at hb ⊢
    have hm := mul_le_mul_of_nonneg_right htu
      (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1+‖u‖) n)
        (norm_nonneg (complexPlaceCubicIntegral rho R theta u)))
    nlinarith
  · simp only [cubicTailWeight,if_neg hreg,mul_one]
    have hb := hs theta u
    linarith

variable {K : Type*} [Field K] [NumberField K]

def cubicProductStationaryWeight (theta : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, Real.sqrt (1+|theta.1 w|)) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖theta.2 w‖)

theorem cubicProductStationaryWeight_pos (theta : mixedSpace K) :
    0 < cubicProductStationaryWeight theta := by
  exact mul_pos (Finset.prod_pos (fun _ _ => Real.sqrt_pos.mpr (by positivity)))
    (Finset.prod_pos (fun _ _ => by positivity))

/-- The literal smooth trace integral has the full product stationary
bound together with arbitrary product-place nonstationary pruning. -/
theorem smoothCubicLinearIntegral_stationary_tail_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      (cubicProductStationaryWeight theta*cubicProductTailWeight R n theta u)*
        ‖smoothCubicLinearIntegral rho R theta u‖ ≤ C := by
  obtain ⟨Cr,hCr,hr⟩ := realPlaceCubicIntegral_stationary_tail_bound rho R hrho hR n
  obtain ⟨Cc,hCc,hc⟩ := complexPlaceCubicIntegral_stationary_tail_bound rho R hrho hR n
  refine ⟨(∏ _ : {w : InfinitePlace K // IsReal w}, Cr) *
      (∏ _ : {w : InfinitePlace K // IsComplex w}, Cc),
    mul_pos (Finset.prod_pos (fun _ _ => hCr)) (Finset.prod_pos (fun _ _ => hCc)),
    fun theta u => ?_⟩
  rw [smoothCubicLinearIntegral_product,norm_mul,norm_prod,norm_prod]
  have he : (cubicProductStationaryWeight theta*cubicProductTailWeight R n theta u)*
      ((∏ w : {w : InfinitePlace K // IsReal w}, ‖realPlaceCubicIntegral rho R (theta.1 w) (u.1 w)‖) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, ‖complexPlaceCubicIntegral rho R (theta.2 w) (u.2 w)‖) =
      (∏ w : {w : InfinitePlace K // IsReal w},
        (Real.sqrt (1+|theta.1 w|)*cubicTailWeight (2*R) n |theta.1 w| |u.1 w|)*
          ‖realPlaceCubicIntegral rho R (theta.1 w) (u.1 w)‖) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        ((1+‖theta.2 w‖)*cubicTailWeight (2*R) n ‖theta.2 w‖ ‖u.2 w‖)*
          ‖complexPlaceCubicIntegral rho R (theta.2 w) (u.2 w)‖ := by
    simp only [cubicProductStationaryWeight,cubicProductTailWeight,Finset.prod_mul_distrib]
    ring
  rw [he]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (cubicTailWeight_pos _ _ _ (abs_nonneg _)).le) (norm_nonneg _)) (fun w _ => hr _ _)
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg (mul_nonneg (by positivity)
      (cubicTailWeight_pos _ _ _ (norm_nonneg _)).le) (norm_nonneg _)) (fun w _ => hc _ _)
  · exact Finset.prod_nonneg (fun w _ => mul_nonneg (mul_nonneg (by positivity)
      (cubicTailWeight_pos _ _ _ (norm_nonneg _)).le) (norm_nonneg _))
  · exact (Finset.prod_pos (fun _ _ => hCr)).le

theorem smoothCubicLinearIntegral_stationary_tail (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      ‖smoothCubicLinearIntegral rho R theta u‖ ≤
        C/(cubicProductStationaryWeight theta*cubicProductTailWeight R n theta u) := by
  obtain ⟨C,hC,hb⟩ := smoothCubicLinearIntegral_stationary_tail_bound (K := K) rho R hrho hR n
  refine ⟨C,hC,fun theta u => (le_div_iff₀ (mul_pos (cubicProductStationaryWeight_pos theta)
    (cubicProductTailWeight_pos R n theta u))).mpr ?_⟩
  simpa only [mul_comm] using hb theta u

theorem smoothCubicLinearIntegral_stationary_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      cubicProductStationaryWeight theta*‖smoothCubicLinearIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothCubicLinearIntegral_stationary_tail_bound (K := K) rho R hrho hR 0
  refine ⟨C,hC,fun theta u => ?_⟩
  have he : cubicProductTailWeight R 0 theta u = 1 := by
    simp only [cubicProductTailWeight,cubicTailWeight,pow_zero,ite_self,Finset.prod_const_one,one_mul]
  simpa only [he,mul_one] using hb theta u

/-- A place-dimension weighted exponent, useful for the weaker one-third
form of the manuscript's oscillatory estimate. -/
def cubicProductFrequencyWeight (exponent : ℝ) (theta : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, (1+|theta.1 w|)^exponent) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖theta.2 w‖)^(2*exponent)

theorem cubicProductFrequencyWeight_pos (exponent : ℝ) (theta : mixedSpace K) :
    0 < cubicProductFrequencyWeight exponent theta := by
  exact mul_pos (Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos (by positivity) _))
    (Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos (by positivity) _))

theorem cubicProductFrequencyWeight_le_stationary {exponent : ℝ} (he : exponent ≤ 1/2)
    (theta : mixedSpace K) :
    cubicProductFrequencyWeight exponent theta ≤ cubicProductStationaryWeight theta := by
  apply mul_le_mul
  · apply Finset.prod_le_prod (fun w _ => (Real.rpow_pos_of_pos (by positivity) _).le)
    intro w hw
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (theta.1 w)]) he
  · apply Finset.prod_le_prod (fun w _ => (Real.rpow_pos_of_pos (by positivity) _).le)
    intro w hw
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ 1+‖theta.2 w‖ by linarith [norm_nonneg (theta.2 w)]) (show 2*exponent ≤ 1 by linarith)
  · exact Finset.prod_nonneg (fun w _ => (Real.rpow_pos_of_pos (by positivity) _).le)
  · exact Finset.prod_nonneg (fun w _ => Real.sqrt_nonneg _)

/-- In particular, the required place exponent d_v/3 holds uniformly for
the actual integral and every linear twist. -/
theorem smoothCubicLinearIntegral_one_third_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      cubicProductFrequencyWeight (1/3) theta*‖smoothCubicLinearIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothCubicLinearIntegral_stationary_bound (K := K) rho R hrho hR
  exact ⟨C,hC,fun theta u =>
    (mul_le_mul_of_nonneg_right (cubicProductFrequencyWeight_le_stationary (by norm_num) theta)
      (norm_nonneg _)).trans (hb theta u)⟩

#print axioms smoothCubicLinearIntegral_stationary_tail
#print axioms smoothCubicLinearIntegral_one_third_bound
end WaringSiegel.WSL3
