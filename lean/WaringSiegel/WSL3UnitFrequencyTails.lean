import WaringSiegel.WSL3UnitPowerProduct

/-!
# Genuine frequency moments and arbitrary-power singular-integral tails

All positive degrees and the exact smooth product source are covered.
The estimates imply one-root frequency L1, every polynomial frequency
moment, and target-uniform quantitative truncation of the singular integral.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [NumberField K]

private theorem real_one_le_fintype_prod {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ i, f i := by
  calc
    (1:ℝ) = ∏ _i : ι, (1:ℝ) := by simp
    _ ≤ ∏ i, f i := Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hf i)

private theorem real_single_le_fintype_prod {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 1 ≤ f i) (a : ι) : f a ≤ ∏ i, f i := by
  calc
    f a = ∏ i : ι, if i = a then f a else 1 := by simp
    _ ≤ ∏ i, f i := by
      apply Finset.prod_le_prod
      · intro i _
        split_ifs <;> linarith [hf a]
      · intro i _
        split_ifs with h
        · exact h ▸ le_rfl
        · exact hf i

theorem powerProductFrequencyWeight_ge_radial (n : ℕ) (theta : mixedSpace K) :
    (1+‖theta‖)^n ≤ powerProductFrequencyWeight n theta := by
  let Pr : ℝ := ∏ w : {w : InfinitePlace K // IsReal w}, (1+|theta.1 w|)
  let Pc : ℝ := ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖theta.2 w‖)
  have hPr : 1 ≤ Pr := real_one_le_fintype_prod _ (fun w => by linarith [abs_nonneg (theta.1 w)])
  have hPc : 1 ≤ Pc := real_one_le_fintype_prod _ (fun w => by linarith [norm_nonneg (theta.2 w)])
  have hP : 1 ≤ Pr*Pc := one_le_mul_of_one_le_of_one_le hPr hPc
  have hreal : ‖theta.1‖ ≤ Pr*Pc-1 := by
    apply (pi_norm_le_iff_of_nonneg (by linarith)).mpr
    intro w
    have hsingle : 1+|theta.1 w| ≤ Pr :=
      real_single_le_fintype_prod (fun w : {w : InfinitePlace K // IsReal w} => 1+|theta.1 w|)
        (fun w => by linarith [abs_nonneg (theta.1 w)]) w
    have hm : Pr ≤ Pr*Pc := le_mul_of_one_le_right (by linarith) hPc
    rw [Real.norm_eq_abs]
    linarith
  have hcomplex : ‖theta.2‖ ≤ Pr*Pc-1 := by
    apply (pi_norm_le_iff_of_nonneg (by linarith)).mpr
    intro w
    have hsingle : 1+‖theta.2 w‖ ≤ Pc :=
      real_single_le_fintype_prod (fun w : {w : InfinitePlace K // IsComplex w} => 1+‖theta.2 w‖)
        (fun w => by linarith [norm_nonneg (theta.2 w)]) w
    have hm : Pc ≤ Pr*Pc := le_mul_of_one_le_left (by linarith) hPr
    linarith
  have hnorm : 1+‖theta‖ ≤ Pr*Pc := by
    rw [Prod.norm_def]
    have hm := max_le hreal hcomplex
    linarith
  have he : powerProductFrequencyWeight n theta = (Pr*Pc)^n := by
    simp only [powerProductFrequencyWeight,Pr,Pc,mul_pow,Finset.prod_pow]
  rw [he]
  exact pow_le_pow_left₀ (by positivity) hnorm n

theorem weightedRootIntegral_radial_rapid_bound (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : mixedSpace K,
      (1+‖theta‖)^n*‖weightedRootIntegral k (smoothRootWeight rho R) theta‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := weightedRootIntegral_product_rapid_bound (K := K) k hk rho R hrho hR n
  exact ⟨C,hC,fun theta => (mul_le_mul_of_nonneg_right
    (powerProductFrequencyWeight_ge_radial n theta) (norm_nonneg _)).trans (hb theta)⟩

theorem weightedRootIntegral_continuous (k : ℕ) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) :
    Continuous (weightedRootIntegral k (smoothRootWeight (K := K) rho R)) := by
  letI := smoothSourceMeasure_finite (K := K) rho R hrho hR
  have he : sourceRootIntegral k (smoothSourceMeasure rho R) =
      weightedRootIntegral k (smoothRootWeight (K := K) rho R) := by
    funext beta
    exact sourceRootIntegral_weighted k _ (smoothRootWeight_contDiff rho R).continuous.measurable
      (smoothRootWeight_nonneg rho R) beta
  rw [← he]
  exact sourceRootIntegral_continuous _ _

/-- Every polynomially weighted modulus of the actual one-root smooth
integral is integrable over the full frequency space. -/
theorem weightedRootIntegral_moment_integrable (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    Integrable (fun beta : mixedSpace K =>
      (1+‖beta‖)^n*‖weightedRootIntegral k (smoothRootWeight rho R) beta‖) := by
  let m := Module.finrank ℝ (mixedSpace K)+1
  have hi : Integrable (fun beta : mixedSpace K => ((1+‖beta‖)^m)⁻¹) := by
    have h := integrable_one_add_norm (E := mixedSpace K) (μ := (volume : Measure (mixedSpace K)))
      (r := (m:ℝ)) (by dsimp only [m]; norm_num)
    convert h using 1
    funext beta
    rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
  obtain ⟨C,hC,hb⟩ := weightedRootIntegral_radial_rapid_bound (K := K) k hk rho R hrho hR (n+m)
  apply (hi.const_mul C).mono'
    (((continuous_const.add continuous_norm).pow n).mul
      (weightedRootIntegral_continuous k rho R hrho hR).norm).aestronglyMeasurable
  filter_upwards [] with beta
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hp : 0 < (1+‖beta‖)^m := by positivity
  apply (le_div_iff₀ hp).mpr
  have h := hb beta
  rw [pow_add] at h
  simpa only [mul_assoc,mul_left_comm,mul_comm,div_eq_mul_inv] using h

theorem weightedRootIntegral_integrable (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) :
    Integrable (weightedRootIntegral k (smoothRootWeight (K := K) rho R)) := by
  apply (integrable_norm_iff (weightedRootIntegral_continuous k rho R hrho hR).aestronglyMeasurable).mp
  simpa only [pow_zero,one_mul] using weightedRootIntegral_moment_integrable (K := K) k hk rho R hrho hR 0

/-- Every positive power has every polynomial frequency moment. -/
theorem weightedRootIntegral_power_moment_integrable (k s : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    Integrable (fun beta : mixedSpace K =>
      (1+‖beta‖)^n*‖weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)‖) := by
  obtain ⟨C,hC,hb⟩ := weightedRootIntegral_radial_rapid_bound (K := K) k hk rho R hrho hR 0
  have hzero (beta : mixedSpace K) : ‖weightedRootIntegral k (smoothRootWeight rho R) beta‖ ≤ C := by
    simpa only [pow_zero,one_mul] using hb beta
  apply ((weightedRootIntegral_moment_integrable (K := K) k hk rho R hrho hR n).const_mul (C^s)).mono'
    (((continuous_const.add continuous_norm).pow n).mul
      ((weightedRootIntegral_continuous k rho R hrho hR).pow (s+1)).norm).aestronglyMeasurable
  filter_upwards [] with beta
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_pow,pow_succ]
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hzero beta) s)
    (mul_nonneg (by positivity : 0 ≤ (1+‖beta‖)^n)
      (norm_nonneg (weightedRootIntegral k (smoothRootWeight rho R) beta)))
  nlinarith

theorem weightedRootIntegral_power_integrable (k s : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) :
    Integrable (fun beta : mixedSpace K => weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)) := by
  apply (integrable_norm_iff ((weightedRootIntegral_continuous k rho R hrho hR).pow (s+1)).aestronglyMeasurable).mp
  simpa only [pow_zero,one_mul] using
    weightedRootIntegral_power_moment_integrable (K := K) k s hk rho R hrho hR 0

theorem weightedRootIntegral_positive_phase_integrable (k s : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (b : mixedSpace K) :
    Integrable (fun beta : mixedSpace K => archimedeanTraceCharacter (-beta) b*
      weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)) := by
  apply (weightedRootIntegral_power_integrable k s hk rho R hrho hR).bdd_mul
  · have hc : Continuous (fun beta : mixedSpace K => archimedeanTraceCharacter (-beta) b) := by
      simpa only [archimedeanTraceCharacter_symm] using
        (archimedeanTraceCharacter_continuous b).comp continuous_neg
    exact hc.aestronglyMeasurable
  · exact ⟨1,fun beta => (archimedeanTraceCharacter_norm (-beta) b).le⟩

/-- Markov's moment estimate for the actual absolute frequency tail,
with constants independent of the target and the truncation radius. -/
theorem weightedRootIntegral_frequency_tail (k s : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q →
      ∫ beta : mixedSpace K in (closedBall 0 Q)ᶜ,
        ‖weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)‖ ≤ C/(1+Q)^n := by
  let F : mixedSpace K → ℝ := fun beta =>
    (1+‖beta‖)^n*‖weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)‖
  have hi : Integrable F := weightedRootIntegral_power_moment_integrable k s hk rho R hrho hR n
  have hF : ∀ beta, 0 ≤ F beta := fun _ => by dsimp only [F]; positivity
  have hIntegral : 0 ≤ ∫ beta, F beta := integral_nonneg hF
  refine ⟨(∫ beta, F beta)+1,by linarith,fun Q hQ => ?_⟩
  have hnorm := (weightedRootIntegral_power_integrable (K := K) k s hk rho R hrho hR).norm
  have hp : 0 < (1+Q)^n := by positivity
  apply (le_div_iff₀ hp).mpr
  have hm : ∫ beta : mixedSpace K in (closedBall 0 Q)ᶜ,
      (1+Q)^n*‖weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)‖ ≤
        ∫ beta : mixedSpace K in (closedBall 0 Q)ᶜ, F beta := by
    apply setIntegral_mono_on (hnorm.const_mul _).integrableOn hi.integrableOn isClosed_closedBall.measurableSet.compl
    intro beta hbeta
    have hb : Q ≤ ‖beta‖ := by
      simp only [Set.mem_compl_iff,mem_closedBall,dist_zero_right] at hbeta
      exact (lt_of_not_ge hbeta).le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith : 1+Q ≤ 1+‖beta‖) n)
      (norm_nonneg _)
  rw [integral_const_mul] at hm
  have hu : (∫ beta : mixedSpace K in (closedBall 0 Q)ᶜ, F beta) ≤ ∫ beta, F beta :=
    setIntegral_le_integral hi (Eventually.of_forall hF)
  nlinarith

def truncatedWeightedSingularIntegral (k s : ℕ) (rho R Q : ℝ) (b : mixedSpace K) : ℂ :=
  ∫ beta in closedBall 0 Q, archimedeanTraceCharacter (-beta) b*
    weightedRootIntegral k (smoothRootWeight rho R) beta^s

/-- Arbitrary-power truncation error for the actual smooth singular
integral, uniform over every target in the mixed space. -/
theorem weightedSingularIntegral_truncation (k s : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q → ∀ b : mixedSpace K,
      ‖weightedSingularIntegral k (s+1) (smoothRootWeight rho R) b -
        truncatedWeightedSingularIntegral k (s+1) rho R Q b‖ ≤ C/(1+Q)^n := by
  obtain ⟨C,hC,hb⟩ := weightedRootIntegral_frequency_tail (K := K) k s hk rho R hrho hR n
  refine ⟨C,hC,fun Q hQ b => ?_⟩
  rw [weightedSingularIntegral,truncatedWeightedSingularIntegral,
    ← setIntegral_compl isClosed_closedBall.measurableSet
      (weightedRootIntegral_positive_phase_integrable k s hk rho R hrho hR b)]
  calc
    _ ≤ ∫ beta : mixedSpace K in (closedBall 0 Q)ᶜ,
        ‖archimedeanTraceCharacter (-beta) b*weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ beta : mixedSpace K in (closedBall 0 Q)ᶜ,
        ‖weightedRootIntegral k (smoothRootWeight rho R) beta^(s+1)‖ := by
      simp only [norm_mul,archimedeanTraceCharacter_norm,one_mul]
    _ ≤ C/(1+Q)^n := hb Q hQ

#print axioms weightedRootIntegral_integrable
#print axioms weightedRootIntegral_power_moment_integrable
#print axioms weightedSingularIntegral_truncation
end WaringSiegel.WSL3
