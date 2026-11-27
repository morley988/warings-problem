import WaringSiegel.WSL3UnitPowerLinearProduct
import WaringSiegel.WSL3UnitCubicPruning

/-!
# Arbitrary-degree product-place linear-frequency pruning

At any subset of places, every inverse power is available once the linear
frequency dominates one plus the power frequency. All other places retain
an actual compact-source norm bound. The resulting mixed product estimate
is uniform in both mixed frequencies.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
open WaringSiegel.WSL3Poisson
set_option maxHeartbeats 800000
variable (k : ℕ)

theorem realPlacePowerLinearIntegral_norm_le (rho R theta u : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ‖realPlacePowerLinearIntegral k rho R theta u‖ ≤ volume.real (closedBall (0:ℝ) (2*R)) := by
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 (2*R))
  · intro x hx
    have hn : positiveSmoothWindow rho R x ≠ 0 := by
      intro hz
      apply hx
      simp only [realPlacePowerLinearKernel, hz, Complex.ofReal_zero, zero_mul]
    have hs := positiveSmoothWindow_support hrho hR hn
    simp only [mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < x)]
    exact hs.2.le
  · intro x
    rw [realPlacePowerLinearKernel_norm k]
    exact positiveSmoothWindow_le_one _ _ _

theorem complexPlacePowerLinearIntegral_norm_le (rho R : ℝ) (theta u : ℂ) (hrho : 0 < rho) (hR : 0 < R) :
    ‖complexPlacePowerLinearIntegral k rho R theta u‖ ≤ volume.real (closedBall (0:ℂ) (2*R)) := by
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 (2*R))
  · intro z hz
    have hn : positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) ≠ 0 := by
      intro he
      apply hz
      simp only [complexPlacePowerLinearKernel, he, Complex.ofReal_zero, zero_mul]
    have hs := positiveSmoothWindow_support (sq_pos_of_pos hrho) (sq_pos_of_pos hR) hn
    rw [Complex.normSq_eq_norm_sq] at hs
    simp only [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg z]
  · intro z
    rw [complexPlacePowerLinearKernel_norm k]
    exact positiveSmoothWindow_le_one _ _ _

/-- An explicit linear-frequency threshold depending only on source radius. -/
def powerLinearTailThreshold (R : ℝ) : ℝ := 1+(powerTailRadius k R)⁻¹

theorem powerLinearTailThreshold_ge_one (R : ℝ) : 1 ≤ powerLinearTailThreshold k R := by
  unfold powerLinearTailThreshold
  have := (inv_pos.mpr (powerTailRadius_pos k R)).le
  linarith

theorem powerLinear_tail_region {R t u : ℝ} (ht : 0 ≤ t)
    (hregion : powerLinearTailThreshold k R*(1+t) ≤ u) :
    1 ≤ u ∧ t ≤ powerTailRadius k R*u := by
  have hB := powerLinearTailThreshold_ge_one k R
  have he := powerTailRadius_pos k R
  have hmult : 1 ≤ powerTailRadius k R*powerLinearTailThreshold k R := by
    rw [powerLinearTailThreshold, mul_add, mul_one, mul_inv_cancel₀ he.ne']
    linarith
  have hu : 1 ≤ u := by nlinarith
  refine ⟨hu, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hregion he.le
  have hprod := mul_le_mul_of_nonneg_right hmult (by linarith : 0 ≤ 1+t)
  nlinarith

/-- The rapid-decay weight at a place. Its arguments are nonnegative sizes. -/
def powerLinearTailWeight (R : ℝ) (n : ℕ) (thetaSize uSize : ℝ) : ℝ :=
  if powerLinearTailThreshold k R*(1+thetaSize) ≤ uSize then (1+uSize)^n else 1

theorem powerLinearTailWeight_pos (R : ℝ) (n : ℕ) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 < powerLinearTailWeight k R n t u := by
  unfold powerLinearTailWeight
  split_ifs <;> positivity

theorem realPlacePowerLinearIntegral_weighted_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      powerLinearTailWeight k (2*R) n |theta| |u| * ‖realPlacePowerLinearIntegral k rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := realPlacePowerLinearIntegral_tail k rho R hrho hR n
  refine ⟨2^n*C+volume.real (closedBall (0:ℝ) (2*R))+1, by positivity, fun theta u => ?_⟩
  unfold powerLinearTailWeight
  split_ifs with hreg
  · have hr := powerLinear_tail_region k (abs_nonneg theta) hreg
    have ht := hb theta u hr.2
    have hm := mul_le_mul_of_nonneg_right (one_add_pow_bound hr.1 n)
      (norm_nonneg (realPlacePowerLinearIntegral k rho R theta u))
    have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2^n)
    nlinarith [measureReal_nonneg (μ := (volume : Measure ℝ)) (s := closedBall 0 (2*R))]
  · rw [one_mul]
    have hb' := realPlacePowerLinearIntegral_norm_le k rho R theta u hrho hR
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

theorem complexPlacePowerLinearIntegral_weighted_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      powerLinearTailWeight k (2*R) n ‖theta‖ ‖u‖ * ‖complexPlacePowerLinearIntegral k rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complexPlacePowerLinearIntegral_tail k rho R hrho hR n
  refine ⟨2^n*C+volume.real (closedBall (0:ℂ) (2*R))+1, by positivity, fun theta u => ?_⟩
  unfold powerLinearTailWeight
  split_ifs with hreg
  · have hr := powerLinear_tail_region k (norm_nonneg theta) hreg
    have ht := hb theta u hr.1 hr.2
    have hm := mul_le_mul_of_nonneg_right (one_add_pow_bound hr.1 n)
      (norm_nonneg (complexPlacePowerLinearIntegral k rho R theta u))
    have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2^n)
    nlinarith [measureReal_nonneg (μ := (volume : Measure ℂ)) (s := closedBall 0 (2*R))]
  · rw [one_mul]
    have hb' := complexPlacePowerLinearIntegral_norm_le k rho R theta u hrho hR
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

variable {K : Type*} [Field K] [NumberField K]

/-- The product of all the placewise rapid-decay weights. -/
def powerLinearProductTailWeight (R : ℝ) (n : ℕ) (theta u : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, powerLinearTailWeight k (2*R) n |theta.1 w| |u.1 w|) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, powerLinearTailWeight k (2*R) n ‖theta.2 w‖ ‖u.2 w‖

theorem powerLinearProductTailWeight_pos (R : ℝ) (n : ℕ) (theta u : mixedSpace K) :
    0 < powerLinearProductTailWeight k R n theta u := by
  exact mul_pos
    (Finset.prod_pos (fun w _ => powerLinearTailWeight_pos k _ _ _ (abs_nonneg _)))
    (Finset.prod_pos (fun w _ => powerLinearTailWeight_pos k _ _ _ (norm_nonneg _)))

/-- Uniform product-place pruning for the literal smooth power trace
integral, with arbitrary subsets of places in the tail region. -/
theorem smoothPowerLinearIntegral_product_tail_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      powerLinearProductTailWeight k R n theta u * ‖smoothPowerLinearIntegral k rho R theta u‖ ≤ C := by
  obtain ⟨Cr,hCr,hr⟩ := realPlacePowerLinearIntegral_weighted_bound k rho R hrho hR n
  obtain ⟨Cc,hCc,hc⟩ := complexPlacePowerLinearIntegral_weighted_bound k rho R hrho hR n
  refine ⟨(∏ _ : {w : InfinitePlace K // IsReal w}, Cr) *
      (∏ _ : {w : InfinitePlace K // IsComplex w}, Cc),
    mul_pos (Finset.prod_pos (fun _ _ => hCr)) (Finset.prod_pos (fun _ _ => hCc)),
    fun theta u => ?_⟩
  rw [smoothPowerLinearIntegral_product k, norm_mul, norm_prod, norm_prod]
  have he : powerLinearProductTailWeight k R n theta u *
      ((∏ w : {w : InfinitePlace K // IsReal w}, ‖realPlacePowerLinearIntegral k rho R (theta.1 w) (u.1 w)‖) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, ‖complexPlacePowerLinearIntegral k rho R (theta.2 w) (u.2 w)‖) =
      (∏ w : {w : InfinitePlace K // IsReal w}, powerLinearTailWeight k (2*R) n |theta.1 w| |u.1 w| *
        ‖realPlacePowerLinearIntegral k rho R (theta.1 w) (u.1 w)‖) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, powerLinearTailWeight k (2*R) n ‖theta.2 w‖ ‖u.2 w‖ *
        ‖complexPlacePowerLinearIntegral k rho R (theta.2 w) (u.2 w)‖ := by
    simp only [powerLinearProductTailWeight, Finset.prod_mul_distrib]
    ring
  rw [he]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg
      (powerLinearTailWeight_pos k _ _ _ (abs_nonneg _)).le (norm_nonneg _)) (fun w _ => hr _ _)
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg
      (powerLinearTailWeight_pos k _ _ _ (norm_nonneg _)).le (norm_nonneg _)) (fun w _ => hc _ _)
  · exact Finset.prod_nonneg (fun w _ => mul_nonneg
      (powerLinearTailWeight_pos k _ _ _ (norm_nonneg _)).le (norm_nonneg _))
  · exact (Finset.prod_pos (fun _ _ => hCr)).le

/-- Division form of the same arbitrary-power product bound. -/
theorem smoothPowerLinearIntegral_product_tail (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      ‖smoothPowerLinearIntegral k rho R theta u‖ ≤ C / powerLinearProductTailWeight k R n theta u := by
  obtain ⟨C,hC,hb⟩ := smoothPowerLinearIntegral_product_tail_bound k (K := K) rho R hrho hR n
  refine ⟨C,hC,fun theta u => (le_div_iff₀ (powerLinearProductTailWeight_pos k R n theta u)).mpr ?_⟩
  simpa only [mul_comm] using hb theta u

#print axioms smoothPowerLinearIntegral_product_tail_bound
#print axioms smoothPowerLinearIntegral_product_tail
end WaringSiegel.WSL3
