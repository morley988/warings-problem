import WaringSiegel.WSL3UnitPairedTruncation

/-! # Fixed compact-region positivity in the actual paired measures

The profile is selected for the whole compact target region. No target-dependent
unit is used, so these quantifiers match the major-integral endgame.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open WaringSiegel.WSL2 WaringSiegel.WSL3
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

theorem pairedSmoothSingularIntegral_ge_box_density
    (a : ℝ) (ha : 0 < a) (k s : ℕ) (hk : 0 < k)
    (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) (b : mixedSpace K) :
    a^(s+1) * continuousArchimedeanDensity k s rho R b ≤
      (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) b).re := by
  letI := smoothSourceMeasure_finite (K := K) rho R hrho hR
  rw [pairedSmoothSingularIntegral_eq_density a ha k s hk rho R hrho hR,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (sourceContinuousDensity_ge_box k s hk rho R (rho/2) (2*R) hrho (half_pos hrho)
      (smoothSourceMeasure_lower rho R hrho hR) (smoothSourceMeasure_upper rho R hrho hR) b)
    (pow_nonneg ha.le _)

/-- A single fixed profile is positive in a neighborhood of every point of
the prescribed compact region, with uniform constants and no unit change. -/
theorem exists_compact_paired_smooth_singularIntegral
    (a : ℝ) (ha : 0 < a) (k s : ℕ) (hk : 0 < k) (B : ℝ) (hB : 0 < B) :
    ∃ rho R c delta : ℝ, 0 < rho ∧ 0 < R ∧ 0 < c ∧ 0 < delta ∧
      ∀ b ∈ compactTargetSet K B, ∀ x ∈ Metric.ball b delta,
        c ≤ (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) x).re ∧
        (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) x).im = 0 := by
  obtain ⟨rho,R,hrho,hR,_,_,_,c,delta,hc,hdelta,hpos⟩ :=
    exists_uniform_continuous_archimedean_density_lower (K := K) k s hk B hB
  refine ⟨rho,R,a^(s+1)*c,delta,hrho,hR,mul_pos (pow_pos ha _) hc,hdelta,?_⟩
  intro b hb x hx
  constructor
  · exact (mul_le_mul_of_nonneg_left (hpos b hb x hx) (pow_nonneg ha.le _)).trans
      (pairedSmoothSingularIntegral_ge_box_density a ha k s hk rho R hrho hR x)
  · rw [pairedSmoothSingularIntegral_eq_density a ha k s hk rho R hrho hR,
      Complex.smul_im, Complex.ofReal_im, smul_zero]

/-- The fixed compact profile has a uniform positive bounded-frequency
truncation in precisely the same paired source and dual measures. -/
theorem exists_compact_positive_truncated_paired_smooth
    (a : ℝ) (ha : 0 < a) (k s : ℕ) (hk : 0 < k) (B : ℝ) (hB : 0 < B) :
    ∃ rho R c Q0 : ℝ, 0 < rho ∧ 0 < R ∧ 0 < c ∧ 0 < Q0 ∧
      ContDiff ℝ ∞ (smoothRootWeight (K := K) rho R) ∧
      HasCompactSupport (smoothRootWeight (K := K) rho R) ∧
      (∀ x : mixedSpace K, 0 ≤ smoothRootWeight rho R x ∧ smoothRootWeight rho R x ≤ 1) ∧
      Function.support (smoothRootWeight (K := K) rho R) ⊆ rootBox K (rho/2) (2*R) ∧
      ∀ b ∈ compactTargetSet K B,
        c ≤ (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) b).re ∧
        (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) b).im = 0 ∧
        ∀ Q : ℝ, Q0 ≤ Q →
          c ≤ (truncatedPairedWeightedSingularIntegral a k (s+2) rho R Q b).re := by
  obtain ⟨rho,R,c,delta,hrho,hR,hc,hdelta,hpos⟩ :=
    exists_compact_paired_smooth_singularIntegral (K := K) a ha k s hk B hB
  obtain ⟨C,hC,herror⟩ := pairedWeightedSingularIntegral_truncation (K := K)
    a ha k (s+1) hk rho R hrho hR 1
  refine ⟨rho,R,c/2,2*C/c,hrho,hR,by positivity,by positivity,
    smoothRootWeight_contDiff rho R,smoothRootWeight_hasCompactSupport rho R hrho hR,
    fun x => ⟨smoothRootWeight_nonneg rho R x,smoothRootWeight_le_one rho R x⟩,
    smoothRootWeight_support_subset rho R hrho hR,?_⟩
  intro b hb
  have hfull := hpos b hb b (Metric.mem_ball_self hdelta)
  refine ⟨by linarith [hfull.1],hfull.2,?_⟩
  intro Q hQ
  have hQpos : 0 ≤ Q := le_trans (by positivity : 0 ≤ 2*C/c) hQ
  have herr := herror Q hQpos b
  simp only [show s+1+1=s+2 by omega,pow_one] at herr
  have hfrac : C/(1+Q) ≤ c/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 1+Q)).mpr
    have hm := (div_le_iff₀ hc).mp hQ
    nlinarith
  have hre := Complex.re_le_norm
    (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight rho R) b -
      truncatedPairedWeightedSingularIntegral a k (s+2) rho R Q b)
  rw [Complex.sub_re] at hre
  linarith [hfull.1]

/-- The profile required for every admissible root count, with the literal
integer-lattice normalization and the chosen compact region. -/
theorem exists_compact_lattice_smooth_singularIntegral
    (k n : ℕ) (hk : 0 < k) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) :
    ∃ rho R c : ℝ, 0 < rho ∧ 0 < R ∧ 0 < c ∧
      ∀ b ∈ compactTargetSet K B,
        c ≤ (pairedWeightedSingularIntegral (integerLatticeSourceScale K) k n
          (smoothRootWeight rho R) b).re ∧
        (pairedWeightedSingularIntegral (integerLatticeSourceScale K) k n
          (smoothRootWeight rho R) b).im = 0 := by
  obtain ⟨rho,R,c,delta,hrho,hR,hc,hdelta,hpos⟩ :=
    exists_compact_paired_smooth_singularIntegral (K := K)
      (integerLatticeSourceScale K) integerLatticeSourceScale_pos k (n-2) hk B hB
  refine ⟨rho,R,c,hrho,hR,hc,?_⟩
  intro b hb
  simpa only [Nat.sub_add_cancel hn] using hpos b hb b (Metric.mem_ball_self hdelta)

#print axioms exists_compact_paired_smooth_singularIntegral
#print axioms exists_compact_positive_truncated_paired_smooth
#print axioms exists_compact_lattice_smooth_singularIntegral
end WaringSiegel.WSL4
