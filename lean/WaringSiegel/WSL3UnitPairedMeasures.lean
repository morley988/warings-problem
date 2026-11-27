import WaringSiegel.WSL3UnitSingularIntegralPositivity

/-!
# Paired Haar measures for the manuscript's trace normalization

If source volume is a times standard mixed volume, its trace-dual frequency
volume is (4^r₂/a) times standard mixed volume. The normalized singular
integral is exactly a^(n-1) times the ordinary continuous image density.
This includes both self-dual measures and lattice-covolume normalization.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

def archimedeanSourceMeasure (a : ℝ) : Measure (mixedSpace K) :=
  ENNReal.ofReal a • volume

def archimedeanDualMeasure (a : ℝ) : Measure (mixedSpace K) :=
  ENNReal.ofReal (((4 : ℝ)^nrComplexPlaces K) / a) • volume

def pairedRootIntegral (a : ℝ) (k : ℕ) (ρ R : ℝ) (β : mixedSpace K) : ℂ :=
  ∫ x in rootBox K ρ R, archimedeanTraceCharacter β (x^k) ∂archimedeanSourceMeasure a

def pairedBoxSingularIntegral (a : ℝ) (k n : ℕ) (ρ R : ℝ) (b : mixedSpace K) : ℂ :=
  ∫ β : mixedSpace K, archimedeanTraceCharacter (-β) b * pairedRootIntegral a k ρ R β ^ n
    ∂archimedeanDualMeasure a

theorem pairedRootIntegral_eq (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (ρ R : ℝ)
    (β : mixedSpace K) :
    pairedRootIntegral a k ρ R β = a • archimedeanRootIntegral k ρ R β := by
  rw [pairedRootIntegral, archimedeanSourceMeasure, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal ha]
  rfl

theorem pairedBoxSingularIntegral_eq (a : ℝ) (ha : 0 < a) (k n : ℕ) (ρ R : ℝ)
    (b : mixedSpace K) :
    pairedBoxSingularIntegral a k n ρ R b =
      (((4 : ℝ)^nrComplexPlaces K) / a * a^n) • archimedeanBoxSingularIntegral k n ρ R b := by
  rw [pairedBoxSingularIntegral, archimedeanDualMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  simp_rw [pairedRootIntegral_eq a ha.le, smul_pow, mul_smul_comm]
  rw [integral_smul, smul_smul]
  rfl

/-- The paired source/frequency convention cancels the trace determinant.
The remaining factor is precisely that of the n-fold image density with
respect to the a-scaled source Haar measure. -/
theorem pairedBoxSingularIntegral_eq_density (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    pairedBoxSingularIntegral a k (s+2) ρ R b =
      a^(s+1) • (continuousArchimedeanDensity k s ρ R b : ℂ) := by
  rw [pairedBoxSingularIntegral_eq a ha,
    archimedeanBoxSingularIntegral_eq_density k s hk ρ R hρ, smul_smul]
  congr 1
  have hD : (4 : ℝ)^nrComplexPlaces K ≠ 0 := by positivity
  field_simp
  ring

theorem pairedRootIntegral_phase_integrable (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    Integrable (fun β : mixedSpace K =>
      archimedeanTraceCharacter (-β) b * pairedRootIntegral a k ρ R β ^ (s+2))
      (archimedeanDualMeasure a) := by
  simp_rw [pairedRootIntegral_eq a ha.le, smul_pow, mul_smul_comm]
  exact ((archimedeanRootIntegral_phase_integrable k s hk ρ R hρ b).smul (a^(s+2))).smul_measure
    ENNReal.ofReal_ne_top

/-- Uniform positive normalized singular integrals for any fixed positive
source Haar scale, including the manuscript's lattice normalization. -/
theorem exists_uniform_paired_target_singularIntegral (a : ℝ) (ha : 0 < a)
    (k s : ℕ) (hk : 0 < k) :
    ∃ ρ R c δ : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧ 0 < δ ∧
      (∀ b : mixedSpace K, Integrable (fun β : mixedSpace K =>
        archimedeanTraceCharacter (-β) b * pairedRootIntegral a k ρ R β ^ (s+2))
          (archimedeanDualMeasure a)) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        ∀ b ∈ Metric.ball (normalizedTarget k u ν) δ,
          c ≤ (pairedBoxSingularIntegral a k (s+2) ρ R b).re ∧
          (pairedBoxSingularIntegral a k (s+2) ρ R b).im = 0 := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, _, _, _, ht⟩ :=
    exists_uniform_normalized_target_density (K := K) k s hk
  refine ⟨ρ, R, a^(s+1)*c, δ, hρ, hR, mul_pos (pow_pos ha _) hc, hδ,
    pairedRootIntegral_phase_integrable a ha k s hk ρ R hρ, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  refine ⟨u, hu, fun b hball => ?_⟩
  rw [pairedBoxSingularIntegral_eq_density a ha k s hk ρ R hρ]
  constructor
  · rw [Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hb b hball) (pow_nonneg ha.le (s+1))
  · rw [Complex.smul_im, Complex.ofReal_im, smul_zero]

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.pairedBoxSingularIntegral_eq_density
#print axioms WaringSiegel.WSL3.exists_uniform_paired_target_singularIntegral
