import WaringSiegel.WSL3UnitFrequencyTails
import WaringSiegel.WSL3UnitSmoothNormalization

/-!
# Paired-measure quantitative truncation and uniform positive major arcs

The source measure is a times ordinary mixed volume and the frequency
measure is its actual trace-dual Haar measure. All scaling factors are
retained, including 4 per complex place before cancellation.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

def truncatedPairedWeightedSingularIntegral (a : ℝ) (k s : ℕ) (rho R Q : ℝ)
    (b : mixedSpace K) : ℂ :=
  ∫ beta in closedBall 0 Q, archimedeanTraceCharacter (-beta) b*
    pairedWeightedRootIntegral a k (smoothRootWeight rho R) beta^s ∂archimedeanDualMeasure a

theorem truncatedPairedWeightedSingularIntegral_eq (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (rho R Q : ℝ) (b : mixedSpace K) :
    truncatedPairedWeightedSingularIntegral a k s rho R Q b =
      (((4:ℝ)^nrComplexPlaces K)/a*a^s) • truncatedWeightedSingularIntegral k s rho R Q b := by
  rw [truncatedPairedWeightedSingularIntegral,archimedeanDualMeasure,Measure.restrict_smul,
    integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
  simp_rw [pairedWeightedRootIntegral_eq a ha.le,smul_pow,mul_smul_comm]
  rw [integral_smul,smul_smul]
  rfl

/-- Arbitrary-power target-uniform truncation in the actual paired Haar
normalization, for every positive degree and every positive root count. -/
theorem pairedWeightedSingularIntegral_truncation (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q → ∀ b : mixedSpace K,
      ‖pairedWeightedSingularIntegral a k (s+1) (smoothRootWeight rho R) b -
        truncatedPairedWeightedSingularIntegral a k (s+1) rho R Q b‖ ≤ C/(1+Q)^n := by
  obtain ⟨C,hC,hb⟩ := weightedSingularIntegral_truncation (K := K) k s hk rho R hrho hR n
  let M : ℝ := ((4:ℝ)^nrComplexPlaces K)/a*a^(s+1)
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M*C,mul_pos hM hC,fun Q hQ b => ?_⟩
  rw [pairedWeightedSingularIntegral_eq a ha,truncatedPairedWeightedSingularIntegral_eq a ha,
    ← smul_sub,_root_.norm_smul,Real.norm_eq_abs,abs_of_pos hM]
  change M*‖weightedSingularIntegral k (s+1) (smoothRootWeight rho R) b-
    truncatedWeightedSingularIntegral k (s+1) rho R Q b‖ ≤ M*C/(1+Q)^n
  have h := mul_le_mul_of_nonneg_left (hb Q hQ b) hM.le
  simpa only [mul_div_assoc] using h

/-- The normalized continuous density is approximated by the actual
truncated Fourier integral with arbitrary polynomial accuracy. -/
theorem pairedDensity_truncation (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q → ∀ b : mixedSpace K,
      ‖a^(s+1) • (sourceContinuousDensity k s (smoothSourceMeasure rho R) b:ℂ) -
        truncatedPairedWeightedSingularIntegral a k (s+2) rho R Q b‖ ≤ C/(1+Q)^n := by
  obtain ⟨C,hC,hb⟩ := pairedWeightedSingularIntegral_truncation (K := K) a ha k (s+1) hk rho R hrho hR n
  refine ⟨C,hC,fun Q hQ b => ?_⟩
  simpa only [show s+1+1=s+2 by omega,pairedSmoothSingularIntegral_eq_density a ha k s hk rho R hrho hR] using hb Q hQ b

/-- One fixed smooth product source has uniformly positive truncated
singular integrals at every unit-balanced target, once Q exceeds one fixed
threshold. This is an actual bounded-frequency singular-integral positivity statement. -/
theorem exists_uniform_positive_truncated_paired_smooth (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) :
    ∃ rho R c Q0 : ℝ, 0 < rho ∧ 0 < R ∧ 0 < c ∧ 0 < Q0 ∧
      ContDiff ℝ ∞ (smoothRootWeight (K := K) rho R) ∧
      HasCompactSupport (smoothRootWeight (K := K) rho R) ∧
      ∀ nu : 𝓞 K, nu ≠ 0 → TotallyPositive nu → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u:𝓞 K) ∧ ∀ Q : ℝ, Q0 ≤ Q →
          c ≤ (truncatedPairedWeightedSingularIntegral a k (s+2) rho R Q
            (normalizedTarget k u nu)).re := by
  obtain ⟨rho,R,c,delta,hrho,hR,hc,hdelta,hs,hcomp,_,_,_,_,hpos⟩ :=
    exists_uniform_paired_smooth_singularIntegral (K := K) a ha k s hk
  obtain ⟨C,hC,hb⟩ := pairedWeightedSingularIntegral_truncation (K := K) a ha k (s+1) hk rho R hrho hR 1
  refine ⟨rho,R,c/2,2*C/c,hrho,hR,by positivity,by positivity,hs,hcomp,?_⟩
  intro nu hnu hp
  obtain ⟨u,hu,htarget⟩ := hpos nu hnu hp
  refine ⟨u,hu,fun Q hQ => ?_⟩
  have hQpos : 0 ≤ Q := le_trans (by positivity : 0 ≤ 2*C/c) hQ
  have herr := hb Q hQpos (normalizedTarget k u nu)
  simp only [show s+1+1=s+2 by omega,pow_one] at herr
  have herror : C/(1+Q) ≤ c/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 1+Q)).mpr
    have hm := (div_le_iff₀ hc).mp hQ
    nlinarith
  have hfull := (htarget _ (Metric.mem_ball_self hdelta)).1
  have hre := Complex.re_le_norm
    (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) (normalizedTarget k u nu)-
      truncatedPairedWeightedSingularIntegral a k (s+2) rho R Q (normalizedTarget k u nu))
  rw [Complex.sub_re] at hre
  linarith

theorem exists_uniform_positive_truncated_lattice_eight_cubes :
    ∃ rho R c Q0 : ℝ, 0 < rho ∧ 0 < R ∧ 0 < c ∧ 0 < Q0 ∧
      ContDiff ℝ ∞ (smoothRootWeight (K := K) rho R) ∧
      HasCompactSupport (smoothRootWeight (K := K) rho R) ∧
      ∀ nu : 𝓞 K, nu ≠ 0 → TotallyPositive nu → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u:𝓞 K) ∧ ∀ Q : ℝ, Q0 ≤ Q →
          c ≤ (truncatedPairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8 rho R Q
            (normalizedTarget 3 u nu)).re := by
  exact exists_uniform_positive_truncated_paired_smooth (integerLatticeSourceScale K)
    integerLatticeSourceScale_pos 3 6 (by norm_num)

#print axioms pairedWeightedSingularIntegral_truncation
#print axioms pairedDensity_truncation
#print axioms exists_uniform_positive_truncated_lattice_eight_cubes
end WaringSiegel.WSL3
