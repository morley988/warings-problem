import WaringSiegel.WSL3UnitTraceInversion
import WaringSiegel.WSL2UnitTargetDensity

/-!
# Uniform positivity of the actual convergent archimedean singular integral

The density lower bound is now a lower bound for the literal frequency
integral, with its proved trace normalization. The root box and positive
constant are fixed before every nonzero totally positive integer target.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem archimedeanBoxSingularIntegral_re (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    (archimedeanBoxSingularIntegral k (s+2) ρ R b).re =
      ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ * continuousArchimedeanDensity k s ρ R b := by
  rw [archimedeanBoxSingularIntegral_eq_density k s hk ρ R hρ]
  rw [Complex.smul_re, Complex.ofReal_re, smul_eq_mul]

theorem archimedeanBoxSingularIntegral_im (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    (archimedeanBoxSingularIntegral k (s+2) ρ R b).im = 0 := by
  rw [archimedeanBoxSingularIntegral_eq_density k s hk ρ R hρ]
  rw [Complex.smul_im, Complex.ofReal_im, smul_zero]

theorem archimedeanBoxSingularIntegral_nonneg (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    0 ≤ (archimedeanBoxSingularIntegral k (s+2) ρ R b).re := by
  rw [archimedeanBoxSingularIntegral_re k s hk ρ R hρ]
  exact mul_nonneg (by positivity) (continuousArchimedeanDensity_nonneg k s ρ R b)

/-- The literal singular integral is a continuous, compactly supported
function of the target. -/
theorem archimedeanBoxSingularIntegral_continuous (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Continuous (archimedeanBoxSingularIntegral (K := K) k (s+2) ρ R) := by
  have he : archimedeanBoxSingularIntegral (K := K) k (s+2) ρ R =
      fun b => ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ •
        (continuousArchimedeanDensity k s ρ R b : ℂ) :=
    funext (archimedeanBoxSingularIntegral_eq_density k s hk ρ R hρ)
  rw [he]
  exact continuous_const.smul
    (Complex.continuous_ofReal.comp (continuousArchimedeanDensity_continuous k s hk ρ R hρ))

/-- Absolute convergence and uniform positive real value for s+2 roots,
with a uniform neighborhood around each actual balanced target. -/
theorem exists_uniform_normalized_target_singularIntegral (k s : ℕ) (hk : 0 < k) :
    ∃ ρ R c δ : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧ 0 < δ ∧
      (∀ b : mixedSpace K, Integrable (fun β : mixedSpace K =>
        archimedeanTraceCharacter (-β) b * archimedeanRootIntegral k ρ R β ^ (s+2))) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        ∀ b ∈ Metric.ball (normalizedTarget k u ν) δ,
          c ≤ (archimedeanBoxSingularIntegral k (s+2) ρ R b).re ∧
          (archimedeanBoxSingularIntegral k (s+2) ρ R b).im = 0 := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, _, _, _, ht⟩ :=
    exists_uniform_normalized_target_density (K := K) k s hk
  refine ⟨ρ, R, ((4 : ℝ)^nrComplexPlaces K)⁻¹*c, δ,
    hρ, hR, mul_pos (by positivity) hc, hδ,
    fun b => archimedeanRootIntegral_phase_integrable k s hk ρ R hρ b, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  refine ⟨u, hu, fun b hball => ⟨?_, archimedeanBoxSingularIntegral_im k s hk ρ R hρ b⟩⟩
  rw [archimedeanBoxSingularIntegral_re k s hk ρ R hρ]
  exact mul_le_mul_of_nonneg_left (hb b hball) (by positivity)

/-- The eight-cube singular integral is genuinely absolutely convergent
and uniformly positive at every actual normalized positive target. -/
theorem exists_uniform_eight_cube_target_singularIntegral :
    ∃ ρ R c : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧
      (∀ b : mixedSpace K, Integrable (fun β : mixedSpace K =>
        archimedeanTraceCharacter (-β) b * archimedeanRootIntegral 3 ρ R β ^ 8)) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        c ≤ (archimedeanBoxSingularIntegral 3 8 ρ R (normalizedTarget 3 u ν)).re ∧
        (archimedeanBoxSingularIntegral 3 8 ρ R (normalizedTarget 3 u ν)).im = 0 := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, hint, ht⟩ :=
    exists_uniform_normalized_target_singularIntegral (K := K) 3 6 (by norm_num)
  refine ⟨ρ, R, c, hρ, hR, hc, hint, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  exact ⟨u, hu, hb _ (Metric.mem_ball_self hδ)⟩

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.exists_uniform_normalized_target_singularIntegral
#print axioms WaringSiegel.WSL3.exists_uniform_eight_cube_target_singularIntegral
