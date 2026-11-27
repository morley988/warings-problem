import WaringSiegel.WSL3PoissonMixedComplementI

/-! # The actual cubic h-sum with its zero shift removed -/
noncomputable section
set_option maxHeartbeats 200000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def compactTraceNonzeroCubicSum (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (q : ArchimedeanTraceTorus K) : ℂ :=
  ∑ x ∈ (compactIntegerSupport w hc P hP).erase 0,
    w (P⁻¹ • mixedEmbedding K (x:K)) * traceTorusCharacter (x^3) q

theorem compactTraceNonzeroCubicSum_eq (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (q : ArchimedeanTraceTorus K) :
    compactTraceNonzeroCubicSum w hc P hP q = compactTraceWeylSum 3 w hc P hP q-w 0 := by
  let S := compactIntegerSupport w hc P hP
  let f : 𝓞 K → ℂ := fun x => w (P⁻¹ • mixedEmbedding K (x:K))*traceTorusCharacter (x^3) q
  have h0 : f 0 = w 0 := by
    simp only [f,map_zero,smul_zero,zero_pow (by norm_num : 3 ≠ 0),
      traceTorusCharacter,map_zero,latticeCharacter_zero,mul_one]
  have hsum : compactTraceWeylSum 3 w hc P hP q = ∑ x ∈ S, f x := by
    exact Finset.sum_coe_sort S f
  rw [hsum]
  change (∑ x ∈ S.erase 0, f x) = _
  by_cases hz : (0:𝓞 K) ∈ S
  · apply eq_sub_iff_add_eq.mpr
    rw [← h0]
    exact Finset.sum_erase_add S f hz
  · have hw0 : w 0 = 0 := by
      by_contra hn
      apply hz
      apply (mem_compactIntegerSupport w hc P hP 0).mpr
      simpa only [map_zero,smul_zero] using hn
    rw [Finset.erase_eq_of_notMem hz,hw0,sub_zero]

theorem compactTraceNonzeroCubicSum_continuous (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) : Continuous (compactTraceNonzeroCubicSum w hc P hP) := by
  have he : compactTraceNonzeroCubicSum w hc P hP =
      fun q => compactTraceWeylSum 3 w hc P hP q-w 0 :=
    funext (compactTraceNonzeroCubicSum_eq w hc P hP)
  rw [he]
  exact (compactTraceWeylSum_continuous _ _ _ _ _).sub continuous_const

theorem compactTraceNonzeroCubicSum_fourth_le (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (q : ArchimedeanTraceTorus K) :
    ‖compactTraceNonzeroCubicSum w hc P hP q‖^4 ≤
      8*(‖compactTraceWeylSum 3 w hc P hP q‖^4+‖w 0‖^4) := by
  rw [compactTraceNonzeroCubicSum_eq]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 4).trans
  convert add_pow_le (norm_nonneg (compactTraceWeylSum 3 w hc P hP q)) (norm_nonneg (w 0)) 4 using 1 <;> norm_num

/-- The excluded-zero cubic Weyl bound, with an arbitrary prescribed
volume-variable epsilon loss. -/
theorem compactTraceNonzeroCubicSum_minor_fourth {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P), ∀ q : ArchimedeanTraceTorus K,
      q ∉ traceMajorArcUnion (P^2*(4*P)) ((6:ℝ)^finrank ℚ K*P^finrank ℚ K) →
      ‖compactTraceNonzeroCubicSum w hc P (by linarith) q‖^4 ≤
        C*(P^finrank ℚ K : ℝ)^(3+ε) := by
  have hd : (0:ℝ) < finrank ℚ K := by exact_mod_cast (finrank_pos (R:=ℚ) (M:=K))
  obtain ⟨C,hC,hb⟩ := compactTraceCubicSum_minor_bound hw hc hsupport (mul_pos hd hε)
  refine ⟨8*(C+‖w 0‖^4),by positivity,fun P hP q hminor => ?_⟩
  have hP0 : 0 < P := by linarith
  have hX : 1 ≤ P^finrank ℚ K := one_le_pow₀ hP
  have hX0 : 0 < P^finrank ℚ K := pow_pos hP0 _
  have hXε : 1 ≤ (P^finrank ℚ K : ℝ)^(3+ε) := Real.one_le_rpow hX (by linarith)
  have heq : (P^finrank ℚ K)^3*P^((finrank ℚ K:ℝ)*ε) = (P^finrank ℚ K:ℝ)^(3+ε) := by
    rw [Real.rpow_mul hP0.le,Real.rpow_natCast,Real.rpow_add hX0,Real.rpow_ofNat]
  have hfull : ‖compactTraceWeylSum 3 w hc P (by linarith) q‖^4 ≤
      C*(P^finrank ℚ K:ℝ)^(3+ε) := by
    exact (hb P hP q hminor).trans_eq (by rw [mul_assoc,heq])
  have hz : ‖w 0‖^4 ≤ ‖w 0‖^4*(P^finrank ℚ K:ℝ)^(3+ε) :=
    le_mul_of_one_le_right (pow_nonneg (norm_nonneg _) _) hXε
  exact (compactTraceNonzeroCubicSum_fourth_le w hc P hP0.ne' q).trans
    ((mul_le_mul_of_nonneg_left (add_le_add hfull hz) (by norm_num : (0:ℝ) ≤ 8)).trans_eq (by ring))

/-- Taking the exact fourth root gives the manuscript's T^(3/4+epsilon). -/
theorem compactTraceNonzeroCubicSum_minor {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P), ∀ q : ArchimedeanTraceTorus K,
      q ∉ traceMajorArcUnion (P^2*(4*P)) ((6:ℝ)^finrank ℚ K*P^finrank ℚ K) →
      ‖compactTraceNonzeroCubicSum w hc P (by linarith) q‖ ≤
        C*(P^finrank ℚ K : ℝ)^((3:ℝ)/4+ε) := by
  obtain ⟨C,hC,hb⟩ := compactTraceNonzeroCubicSum_minor_fourth hw hc hsupport
    (show 0 < 4*ε by linarith)
  refine ⟨C^((1:ℝ)/4),Real.rpow_pos_of_pos hC _,fun P hP q hminor => ?_⟩
  have hP0 : 0 < P := by linarith
  have hX0 : 0 < P^finrank ℚ K := pow_pos hP0 _
  have hb4 := hb P hP q hminor
  have hroot : ‖compactTraceNonzeroCubicSum w hc P (by linarith) q‖ ≤
      (C*(P^finrank ℚ K:ℝ)^(3+4*ε))^((1:ℝ)/4) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by positivity) (by norm_num : (0:ℝ)<4)).mpr
    simpa only [Real.rpow_ofNat] using hb4
  apply hroot.trans_eq
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hX0.le _),← Real.rpow_mul hX0.le]
  congr 2
  ring

end WaringSiegel.WSL3Poisson
