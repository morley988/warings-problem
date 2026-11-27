import WaringSiegel.WSL3UnitSmoothSchwartz
import WaringSiegel.WSL3UnitLatticeNormalization

/-!
# The positive smooth singular integral with the manuscript's paired measures

The source measure is actual integral-basis coordinate Lebesgue measure;
the frequency measure is its paired trace-dual measure. The fixed smooth
product profile has actual absolute convergence, exact inversion, and a
uniform positive lower bound at every unit-balanced target.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

def pairedWeightedRootIntegral (a : ℝ) (k : ℕ) (w : mixedSpace K → ℝ) (β : mixedSpace K) : ℂ :=
  ∫ x, w x • archimedeanTraceCharacter β (x^k) ∂archimedeanSourceMeasure a

def pairedWeightedSingularIntegral (a : ℝ) (k n : ℕ) (w : mixedSpace K → ℝ)
    (b : mixedSpace K) : ℂ :=
  ∫ β, archimedeanTraceCharacter (-β) b * pairedWeightedRootIntegral a k w β ^ n
    ∂archimedeanDualMeasure a

theorem pairedWeightedRootIntegral_eq (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (w : mixedSpace K → ℝ) (β : mixedSpace K) :
    pairedWeightedRootIntegral a k w β = a • weightedRootIntegral k w β := by
  rw [pairedWeightedRootIntegral, archimedeanSourceMeasure,
    integral_smul_measure, ENNReal.toReal_ofReal ha]
  rfl

theorem pairedWeightedSingularIntegral_eq (a : ℝ) (ha : 0 < a) (k n : ℕ)
    (w : mixedSpace K → ℝ) (b : mixedSpace K) :
    pairedWeightedSingularIntegral a k n w b =
      (((4 : ℝ)^nrComplexPlaces K) / a * a^n) • weightedSingularIntegral k n w b := by
  rw [pairedWeightedSingularIntegral, archimedeanDualMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  simp_rw [pairedWeightedRootIntegral_eq a ha.le, smul_pow, mul_smul_comm]
  rw [integral_smul, smul_smul]
  rfl

/-- Exact inversion for the literal smooth profile under paired Haar measures. -/
theorem pairedSmoothSingularIntegral_eq_density (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (b : mixedSpace K) :
    pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight ρ R) b =
      a^(s+1) • (sourceContinuousDensity k s (smoothSourceMeasure ρ R) b : ℂ) := by
  rw [pairedWeightedSingularIntegral_eq a ha,
    smoothWeightedSingularIntegral_eq_density k s hk ρ R hρ hR, smul_smul]
  congr 1
  have hD : (4 : ℝ)^nrComplexPlaces K ≠ 0 := by positivity
  field_simp
  ring

theorem pairedSmooth_phase_integrable (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (b : mixedSpace K) :
    Integrable (fun β : mixedSpace K => archimedeanTraceCharacter (-β) b *
      pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β ^ (s+2))
        (archimedeanDualMeasure a) := by
  simp_rw [pairedWeightedRootIntegral_eq a ha.le, smul_pow, mul_smul_comm]
  exact ((smoothWeighted_phase_integrable k s hk ρ R hρ hR b).smul (a^(s+2))).smul_measure
    ENNReal.ofReal_ne_top

/-- The full smooth-profile archimedean positivity conclusion with an
arbitrary fixed positive source Haar normalization. -/
theorem exists_uniform_paired_smooth_singularIntegral (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) :
    ∃ ρ R c δ : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧ 0 < δ ∧
      ContDiff ℝ ∞ (smoothRootWeight (K := K) ρ R) ∧
      HasCompactSupport (smoothRootWeight (K := K) ρ R) ∧
      (∀ x : mixedSpace K, 0 ≤ smoothRootWeight ρ R x ∧ smoothRootWeight ρ R x ≤ 1) ∧
      Function.support (smoothRootWeight (K := K) ρ R) ⊆ rootBox K (ρ/2) (2*R) ∧
      (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : mixedSpace K,
        ‖iteratedFDeriv ℝ n (smoothRootWeight ρ R) x‖ ≤ C) ∧
      (∀ b : mixedSpace K, Integrable (fun β : mixedSpace K =>
        archimedeanTraceCharacter (-β) b * pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β ^ (s+2))
          (archimedeanDualMeasure a)) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        ∀ b ∈ Metric.ball (normalizedTarget k u ν) δ,
          c ≤ (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight ρ R) b).re ∧
          (pairedWeightedSingularIntegral a k (s+2) (smoothRootWeight ρ R) b).im = 0 := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, hs, hcomp, h01, hsupp, _, ht⟩ :=
    exists_uniform_smooth_product_singularIntegral (K := K) k s hk
  let C : ℝ := ((4 : ℝ)^nrComplexPlaces K) / a * a^(s+2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨ρ, R, C*c, δ, hρ, hR, mul_pos hC hc, hδ, hs, hcomp, h01, hsupp,
    smoothRootWeight_derivative_bound ρ R hρ hR,
    pairedSmooth_phase_integrable a ha k s hk ρ R hρ hR, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  refine ⟨u, hu, fun b hball => ?_⟩
  rw [pairedWeightedSingularIntegral_eq a ha]
  constructor
  · rw [Complex.smul_re, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hb b hball).1 hC.le
  · rw [Complex.smul_im, (hb b hball).2, smul_zero]

/-- Exact eight-cube specialization in the manuscript's integral-basis and
trace-dual Haar measures. All profile, convergence, and positivity hypotheses
have been discharged for the explicit fixed smooth product weight. -/
theorem exists_uniform_lattice_smooth_eight_cube_singularIntegral :
    ∃ ρ R c : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧
      ContDiff ℝ ∞ (smoothRootWeight (K := K) ρ R) ∧
      HasCompactSupport (smoothRootWeight (K := K) ρ R) ∧
      Function.support (smoothRootWeight (K := K) ρ R) ⊆ rootBox K (ρ/2) (2*R) ∧
      (∀ b : mixedSpace K, Integrable (fun β : mixedSpace K =>
        archimedeanTraceCharacter (-β) b *
          pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight ρ R) β ^ 8)
            (archimedeanDualMeasure (integerLatticeSourceScale K))) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        c ≤ (pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
          (smoothRootWeight ρ R) (normalizedTarget 3 u ν)).re ∧
        (pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
          (smoothRootWeight ρ R) (normalizedTarget 3 u ν)).im = 0 := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, hs, hcomp, _, hsupp, _, hint, ht⟩ :=
    exists_uniform_paired_smooth_singularIntegral (K := K)
      (integerLatticeSourceScale K) integerLatticeSourceScale_pos 3 6 (by norm_num)
  refine ⟨ρ, R, c, hρ, hR, hc, hs, hcomp, hsupp, hint, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  exact ⟨u, hu, hb _ (Metric.mem_ball_self hδ)⟩

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.pairedSmoothSingularIntegral_eq_density
#print axioms WaringSiegel.WSL3.exists_uniform_paired_smooth_singularIntegral
#print axioms WaringSiegel.WSL3.exists_uniform_lattice_smooth_eight_cube_singularIntegral
