import WaringSiegel.WSL4ArchLocalTails

/-! # Simultaneous stationary decay and rapid product tails of the near-zero source -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

theorem cubic_stationary_tail_combine {e R t u I Cs Ct : ℝ} (he : e ≤ 1)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hI : 0 ≤ I) (hCs : 0 ≤ Cs) (hCt : 0 ≤ Ct)
    (n : ℕ) (hs : (1+t)^e*I ≤ Cs)
    (hrapid : cubicTailWeight R (n+1) t u * I ≤ Ct) :
    ((1+t)^e*cubicTailWeight R n t u)*I ≤ Cs+Ct := by
  by_cases hreg : cubicTailThreshold R*(1+t) ≤ u
  · have hB := cubicTailThreshold_ge_one R
    have htu : 1+t ≤ 1+u := by nlinarith
    have hrpow : (1+t)^e ≤ 1+u := calc
      _ ≤ (1+t)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ = 1+t := Real.rpow_one _
      _ ≤ _ := htu
    simp only [cubicTailWeight,if_pos hreg,pow_succ] at hrapid ⊢
    have hm := mul_le_mul_of_nonneg_right hrpow
      (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1+u) n) hI)
    nlinarith
  · simp only [cubicTailWeight,if_neg hreg,mul_one]
    linarith

theorem nearZeroRealCubicIntegral_stationary_tail (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      ((1+|theta|)^((1:ℝ)/3)*cubicTailWeight 1 n |theta| |u|)*
        ‖nearZeroRealCubicIntegral theta u‖ ≤ C := by
  obtain ⟨Cs,hCs,hs⟩ := nearZeroRealCubicIntegral_stationary
  obtain ⟨Ct,hCt,ht⟩ := nearZeroRealCubicIntegral_weighted_bound (n+1)
  exact ⟨Cs+Ct,by positivity,fun theta u =>
    cubic_stationary_tail_combine (by norm_num) (abs_nonneg theta) (abs_nonneg u)
      (norm_nonneg _) hCs.le hCt.le n (hs theta u) (ht theta u)⟩

theorem nearZeroComplexCubicIntegral_stationary_tail (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      ((1+‖theta‖)^((2:ℝ)/3)*cubicTailWeight 1 n ‖theta‖ ‖u‖)*
        ‖nearZeroComplexCubicIntegral theta u‖ ≤ C := by
  obtain ⟨Cs,hCs,hs⟩ := nearZeroComplexCubicIntegral_stationary
  obtain ⟨Ct,hCt,ht⟩ := nearZeroComplexCubicIntegral_weighted_bound (n+1)
  exact ⟨Cs+Ct,by positivity,fun theta u =>
    cubic_stationary_tail_combine (by norm_num) (norm_nonneg theta) (norm_nonneg u)
      (norm_nonneg _) hCs.le hCt.le n (hs theta u) (ht theta u)⟩

variable {K : Type*} [Field K] [NumberField K]

/-- The actual near-zero mixed integral retains arbitrary powers in every
linear-dominant place, simultaneously with its d_v/3 stationary factor. -/
theorem nearZeroCubicLinearIntegral_stationary_tail_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      (cubicProductFrequencyWeight (1/3) theta*cubicProductTailWeight (1/2) n theta u)*
        ‖nearZeroCubicLinearIntegral theta u‖ ≤ C := by
  obtain ⟨Cr,hCr,hr⟩ := nearZeroRealCubicIntegral_stationary_tail n
  obtain ⟨Cc,hCc,hc⟩ := nearZeroComplexCubicIntegral_stationary_tail n
  refine ⟨(∏ _ : {w : InfinitePlace K // IsReal w}, Cr) *
      (∏ _ : {w : InfinitePlace K // IsComplex w}, Cc),
    mul_pos (Finset.prod_pos (fun _ _ => hCr)) (Finset.prod_pos (fun _ _ => hCc)),
    fun theta u => ?_⟩
  rw [nearZeroCubicLinearIntegral_product,norm_mul,norm_prod,norm_prod]
  have he : (cubicProductFrequencyWeight (1/3) theta*cubicProductTailWeight (1/2) n theta u)*
      ((∏ w : {w : InfinitePlace K // IsReal w}, ‖nearZeroRealCubicIntegral (theta.1 w) (u.1 w)‖) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, ‖nearZeroComplexCubicIntegral (theta.2 w) (u.2 w)‖) =
      (∏ w : {w : InfinitePlace K // IsReal w},
        ((1+|theta.1 w|)^((1:ℝ)/3)*cubicTailWeight 1 n |theta.1 w| |u.1 w|)*
          ‖nearZeroRealCubicIntegral (theta.1 w) (u.1 w)‖) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        ((1+‖theta.2 w‖)^((2:ℝ)/3)*cubicTailWeight 1 n ‖theta.2 w‖ ‖u.2 w‖)*
          ‖nearZeroComplexCubicIntegral (theta.2 w) (u.2 w)‖ := by
    simp only [cubicProductFrequencyWeight,cubicProductTailWeight,Finset.prod_mul_distrib]
    norm_num
    ring
  rw [he]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg (mul_nonneg (by positivity)
      (cubicTailWeight_pos _ _ _ (abs_nonneg _)).le) (norm_nonneg _)) (fun w _ => hr _ _)
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg (mul_nonneg (by positivity)
      (cubicTailWeight_pos _ _ _ (norm_nonneg _)).le) (norm_nonneg _)) (fun w _ => hc _ _)
  · exact Finset.prod_nonneg (fun w _ => mul_nonneg (mul_nonneg (by positivity)
      (cubicTailWeight_pos _ _ _ (norm_nonneg _)).le) (norm_nonneg _))
  · exact (Finset.prod_pos (fun _ _ => hCr)).le

theorem nearZeroCubicLinearIntegral_stationary_tail (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      ‖nearZeroCubicLinearIntegral theta u‖ ≤
        C/(cubicProductFrequencyWeight (1/3) theta*cubicProductTailWeight (1/2) n theta u) := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubicLinearIntegral_stationary_tail_bound (K:=K) n
  refine ⟨C,hC,fun theta u => (le_div_iff₀ (mul_pos
    (cubicProductFrequencyWeight_pos _ theta) (cubicProductTailWeight_pos _ n theta u))).mpr ?_⟩
  simpa only [mul_comm] using hb theta u

#print axioms nearZeroCubicLinearIntegral_stationary_tail
end WaringSiegel.WSL4

