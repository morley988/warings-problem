import WaringSiegel.WSL3UnitCubicProduct

/-!
# Uniform product-place nonstationary pruning weights

Each place contributes arbitrary rapid decay once its linear frequency
exceeds a fixed multiple of one plus its cubic frequency. Places outside
that region retain the uniform compact-source bound. Their product is a
uniform bound for the literal mixed trace integral, with no assumptions on
which subset of places lies in the nonstationary region.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
set_option maxHeartbeats 800000

/-- Compact support and a pointwise unit bound control the actual integral. -/
theorem compact_integral_norm_le_volume {E : Type*} [NormedAddCommGroup E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    {S : Set E} (hS : IsCompact S) {f : E → ℂ}
    (hfs : support f ⊆ S) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, f x‖ ≤ volume.real S := by
  have he : (∫ x in S, f x) = ∫ x, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      by_contra hn
      exact hx (hfs hn)
  rw [← he]
  simpa only [one_mul] using norm_setIntegral_le_of_norm_le_const_ae
    (μ := (volume : Measure E)) hS.measure_lt_top (Eventually.of_forall hf)

theorem realPlaceCubicIntegral_norm_le (rho R theta u : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ‖realPlaceCubicIntegral rho R theta u‖ ≤ volume.real (closedBall (0:ℝ) (2*R)) := by
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 (2*R))
  · intro x hx
    have hn : positiveSmoothWindow rho R x ≠ 0 := by
      intro hz
      apply hx
      simp only [realPlaceCubicKernel, hz, Complex.ofReal_zero, zero_mul]
    have hs := positiveSmoothWindow_support hrho hR hn
    simp only [mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < x)]
    exact hs.2.le
  · intro x
    rw [realPlaceCubicKernel_norm]
    exact positiveSmoothWindow_le_one _ _ _

theorem complexPlaceCubicIntegral_norm_le (rho R : ℝ) (theta u : ℂ) (hrho : 0 < rho) (hR : 0 < R) :
    ‖complexPlaceCubicIntegral rho R theta u‖ ≤ volume.real (closedBall (0:ℂ) (2*R)) := by
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 (2*R))
  · intro z hz
    have hn : positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) ≠ 0 := by
      intro he
      apply hz
      simp only [complexPlaceCubicKernel, he, Complex.ofReal_zero, zero_mul]
    have hs := positiveSmoothWindow_support (sq_pos_of_pos hrho) (sq_pos_of_pos hR) hn
    rw [Complex.normSq_eq_norm_sq] at hs
    simp only [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg z]
  · intro z
    rw [complexPlaceCubicKernel_norm]
    exact positiveSmoothWindow_le_one _ _ _

/-- An explicit linear-frequency threshold depending only on source radius. -/
def cubicTailThreshold (R : ℝ) : ℝ := 1+(cubicTailRadius R)⁻¹

theorem cubicTailThreshold_ge_one (R : ℝ) : 1 ≤ cubicTailThreshold R := by
  unfold cubicTailThreshold
  have := (inv_pos.mpr (cubicTailRadius_pos R)).le
  linarith

theorem cubic_tail_region {R t u : ℝ} (ht : 0 ≤ t)
    (hregion : cubicTailThreshold R*(1+t) ≤ u) :
    1 ≤ u ∧ t ≤ cubicTailRadius R*u := by
  have hB := cubicTailThreshold_ge_one R
  have he := cubicTailRadius_pos R
  have hmult : 1 ≤ cubicTailRadius R*cubicTailThreshold R := by
    rw [cubicTailThreshold, mul_add, mul_one, mul_inv_cancel₀ he.ne']
    linarith
  have hu : 1 ≤ u := by nlinarith
  refine ⟨hu, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hregion he.le
  have hprod := mul_le_mul_of_nonneg_right hmult (by linarith : 0 ≤ 1+t)
  nlinarith

/-- The rapid-decay weight at a place. Its arguments are nonnegative sizes. -/
def cubicTailWeight (R : ℝ) (n : ℕ) (thetaSize uSize : ℝ) : ℝ :=
  if cubicTailThreshold R*(1+thetaSize) ≤ uSize then (1+uSize)^n else 1

theorem cubicTailWeight_pos (R : ℝ) (n : ℕ) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 < cubicTailWeight R n t u := by
  unfold cubicTailWeight
  split_ifs <;> positivity

theorem one_add_pow_bound {u : ℝ} (hu : 1 ≤ u) (n : ℕ) :
    (1+u)^n ≤ 2^n*u^n := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

theorem realPlaceCubicIntegral_weighted_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      cubicTailWeight (2*R) n |theta| |u| * ‖realPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := realPlaceCubicIntegral_tail rho R hrho hR n
  refine ⟨2^n*C+volume.real (closedBall (0:ℝ) (2*R))+1, by positivity, fun theta u => ?_⟩
  unfold cubicTailWeight
  split_ifs with hreg
  · have hr := cubic_tail_region (abs_nonneg theta) hreg
    have ht := hb theta u hr.2
    have hm := mul_le_mul_of_nonneg_right (one_add_pow_bound hr.1 n)
      (norm_nonneg (realPlaceCubicIntegral rho R theta u))
    have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2^n)
    nlinarith [measureReal_nonneg (μ := (volume : Measure ℝ)) (s := closedBall 0 (2*R))]
  · rw [one_mul]
    have hb' := realPlaceCubicIntegral_norm_le rho R theta u hrho hR
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

theorem complexPlaceCubicIntegral_weighted_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      cubicTailWeight (2*R) n ‖theta‖ ‖u‖ * ‖complexPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complexPlaceCubicIntegral_tail rho R hrho hR n
  refine ⟨2^n*C+volume.real (closedBall (0:ℂ) (2*R))+1, by positivity, fun theta u => ?_⟩
  unfold cubicTailWeight
  split_ifs with hreg
  · have hr := cubic_tail_region (norm_nonneg theta) hreg
    have ht := hb theta u hr.1 hr.2
    have hm := mul_le_mul_of_nonneg_right (one_add_pow_bound hr.1 n)
      (norm_nonneg (complexPlaceCubicIntegral rho R theta u))
    have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2^n)
    nlinarith [measureReal_nonneg (μ := (volume : Measure ℂ)) (s := closedBall 0 (2*R))]
  · rw [one_mul]
    have hb' := complexPlaceCubicIntegral_norm_le rho R theta u hrho hR
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

variable {K : Type*} [Field K] [NumberField K]

/-- The product of all the placewise rapid-decay weights. -/
def cubicProductTailWeight (R : ℝ) (n : ℕ) (theta u : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, cubicTailWeight (2*R) n |theta.1 w| |u.1 w|) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, cubicTailWeight (2*R) n ‖theta.2 w‖ ‖u.2 w‖

theorem cubicProductTailWeight_pos (R : ℝ) (n : ℕ) (theta u : mixedSpace K) :
    0 < cubicProductTailWeight R n theta u := by
  exact mul_pos
    (Finset.prod_pos (fun w _ => cubicTailWeight_pos _ _ _ (abs_nonneg _)))
    (Finset.prod_pos (fun w _ => cubicTailWeight_pos _ _ _ (norm_nonneg _)))

/-- Uniform product-place pruning for the literal smooth cubic trace
integral, with arbitrary subsets of places in the tail region. -/
theorem smoothCubicLinearIntegral_product_tail_bound (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      cubicProductTailWeight R n theta u * ‖smoothCubicLinearIntegral rho R theta u‖ ≤ C := by
  obtain ⟨Cr,hCr,hr⟩ := realPlaceCubicIntegral_weighted_bound rho R hrho hR n
  obtain ⟨Cc,hCc,hc⟩ := complexPlaceCubicIntegral_weighted_bound rho R hrho hR n
  refine ⟨(∏ _ : {w : InfinitePlace K // IsReal w}, Cr) *
      (∏ _ : {w : InfinitePlace K // IsComplex w}, Cc),
    mul_pos (Finset.prod_pos (fun _ _ => hCr)) (Finset.prod_pos (fun _ _ => hCc)),
    fun theta u => ?_⟩
  rw [smoothCubicLinearIntegral_product, norm_mul, norm_prod, norm_prod]
  have he : cubicProductTailWeight R n theta u *
      ((∏ w : {w : InfinitePlace K // IsReal w}, ‖realPlaceCubicIntegral rho R (theta.1 w) (u.1 w)‖) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, ‖complexPlaceCubicIntegral rho R (theta.2 w) (u.2 w)‖) =
      (∏ w : {w : InfinitePlace K // IsReal w}, cubicTailWeight (2*R) n |theta.1 w| |u.1 w| *
        ‖realPlaceCubicIntegral rho R (theta.1 w) (u.1 w)‖) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, cubicTailWeight (2*R) n ‖theta.2 w‖ ‖u.2 w‖ *
        ‖complexPlaceCubicIntegral rho R (theta.2 w) (u.2 w)‖ := by
    simp only [cubicProductTailWeight, Finset.prod_mul_distrib]
    ring
  rw [he]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg
      (cubicTailWeight_pos _ _ _ (abs_nonneg _)).le (norm_nonneg _)) (fun w _ => hr _ _)
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg
      (cubicTailWeight_pos _ _ _ (norm_nonneg _)).le (norm_nonneg _)) (fun w _ => hc _ _)
  · exact Finset.prod_nonneg (fun w _ => mul_nonneg
      (cubicTailWeight_pos _ _ _ (norm_nonneg _)).le (norm_nonneg _))
  · exact (Finset.prod_pos (fun _ _ => hCr)).le

/-- Division form of the same arbitrary-power product bound. -/
theorem smoothCubicLinearIntegral_product_tail (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      ‖smoothCubicLinearIntegral rho R theta u‖ ≤ C / cubicProductTailWeight R n theta u := by
  obtain ⟨C,hC,hb⟩ := smoothCubicLinearIntegral_product_tail_bound (K := K) rho R hrho hR n
  refine ⟨C,hC,fun theta u => (le_div_iff₀ (cubicProductTailWeight_pos R n theta u)).mpr ?_⟩
  simpa only [mul_comm] using hb theta u

#print axioms smoothCubicLinearIntegral_product_tail_bound
#print axioms smoothCubicLinearIntegral_product_tail
end WaringSiegel.WSL3
