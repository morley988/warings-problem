import WaringSiegel.WSL3UnitSourceInversion
import WaringSiegel.WSL3UnitSmoothCutoff
import WaringSiegel.WSL3UnitSingularIntegralPositivity

/-!
# The smooth product profile and its actual positive singular integral

The explicit smooth product weight lies between the inner-box indicator and
the outer-box indicator. Its source measure therefore has a genuine L² image
density, and the already proved source inversion identifies its actual
weighted oscillatory integral. Positivity is transferred by measure and
positive-convolution domination, never by changing profile notation.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

def weightedSourceMeasure (w : mixedSpace K → ℝ) : Measure (mixedSpace K) :=
  volume.withDensity (fun x => ENNReal.ofReal (w x))

def weightedRootIntegral (k : ℕ) (w : mixedSpace K → ℝ) (β : mixedSpace K) : ℂ :=
  ∫ x, w x • archimedeanTraceCharacter β (x^k)

def weightedSingularIntegral (k n : ℕ) (w : mixedSpace K → ℝ) (b : mixedSpace K) : ℂ :=
  ∫ β, archimedeanTraceCharacter (-β) b * weightedRootIntegral k w β ^ n

def smoothSourceMeasure (ρ R : ℝ) : Measure (mixedSpace K) :=
  weightedSourceMeasure (smoothRootWeight ρ R)

theorem sourceRootIntegral_weighted (k : ℕ) (w : mixedSpace K → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (β : mixedSpace K) :
    sourceRootIntegral k (weightedSourceMeasure w) β = weightedRootIntegral k w β := by
  rw [sourceRootIntegral, weightedSourceMeasure,
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw0 _), weightedRootIntegral]

/-- The source weight genuinely majorizes the inner positive box. -/
theorem smoothSourceMeasure_lower (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    volume.restrict (rootBox K ρ R) ≤ smoothSourceMeasure (K := K) ρ R := by
  rw [← withDensity_indicator_one (rootBox_isCompact (K := K) ρ R).measurableSet]
  apply withDensity_mono
  filter_upwards with x
  by_cases hx : x ∈ rootBox K ρ R
  · rw [Set.indicator_of_mem hx, smoothRootWeight_eq_one ρ R hρ hR hx, ENNReal.ofReal_one]
    exact le_rfl
  · rw [Set.indicator_of_notMem hx]
    exact zero_le _

/-- The source weight is controlled by an outer box still separated from zero. -/
theorem smoothSourceMeasure_upper (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    smoothSourceMeasure (K := K) ρ R ≤ volume.restrict (rootBox K (ρ/2) (2*R)) := by
  rw [← withDensity_indicator_one (rootBox_isCompact (K := K) (ρ/2) (2*R)).measurableSet]
  apply withDensity_mono
  filter_upwards with x
  by_cases hx : x ∈ rootBox K (ρ/2) (2*R)
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.ofReal_le_one.mpr (smoothRootWeight_le_one ρ R x)
  · have hz : smoothRootWeight ρ R x = 0 := by
      by_contra hn
      exact hx (smoothRootWeight_support_subset ρ R hρ hR hn)
    rw [hz, ENNReal.ofReal_zero, Set.indicator_of_notMem hx]

theorem smoothSourceMeasure_finite (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    IsFiniteMeasure (smoothSourceMeasure (K := K) ρ R) := by
  letI : IsFiniteMeasure (volume.restrict (rootBox K (ρ/2) (2*R))) :=
    isFiniteMeasure_restrict.mpr (rootBox_isCompact (K := K) (ρ/2) (2*R)).measure_lt_top.ne
  exact isFiniteMeasure_of_le _ (smoothSourceMeasure_upper ρ R hρ hR)

/-- The smooth weighted singular integral is absolutely convergent, proved
from its genuine source-image density rather than a decay assumption. -/
theorem smoothWeighted_phase_integrable (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (b : mixedSpace K) :
    Integrable (fun β : mixedSpace K => archimedeanTraceCharacter (-β) b *
      weightedRootIntegral k (smoothRootWeight ρ R) β ^ (s+2)) := by
  letI := smoothSourceMeasure_finite (K := K) ρ R hρ hR
  have h := sourceRootIntegral_phase_integrable k s hk (ρ/2) (2*R) (half_pos hρ)
    (smoothSourceMeasure_upper (K := K) ρ R hρ hR) b
  have heq (β : mixedSpace K) : sourceRootIntegral k (smoothSourceMeasure ρ R) β =
      weightedRootIntegral k (smoothRootWeight ρ R) β :=
    sourceRootIntegral_weighted k _ (smoothRootWeight_contDiff ρ R).continuous.measurable
      (smoothRootWeight_nonneg ρ R) β
  simpa only [heq] using h

/-- Fourier inversion for the exact smooth product weight. -/
theorem smoothWeightedSingularIntegral_eq_density (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (b : mixedSpace K) :
    weightedSingularIntegral k (s+2) (smoothRootWeight ρ R) b =
      ((4 : ℝ)^nrComplexPlaces K)⁻¹ •
        (sourceContinuousDensity k s (smoothSourceMeasure ρ R) b : ℂ) := by
  letI := smoothSourceMeasure_finite (K := K) ρ R hρ hR
  have h := sourceSingularIntegral_eq_density k s hk (ρ/2) (2*R) (half_pos hρ)
    (smoothSourceMeasure_upper (K := K) ρ R hρ hR) b
  have heq (β : mixedSpace K) : sourceRootIntegral k (smoothSourceMeasure ρ R) β =
      weightedRootIntegral k (smoothRootWeight ρ R) β :=
    sourceRootIntegral_weighted k _ (smoothRootWeight_contDiff ρ R).continuous.measurable
      (smoothRootWeight_nonneg ρ R) β
  simpa only [sourceSingularIntegral, heq, weightedSingularIntegral] using h

/-- A proved comparison between distinct source profiles. -/
theorem smoothWeightedSingularIntegral_ge_box (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (b : mixedSpace K) :
    (archimedeanBoxSingularIntegral k (s+2) ρ R b).re ≤
      (weightedSingularIntegral k (s+2) (smoothRootWeight ρ R) b).re := by
  letI := smoothSourceMeasure_finite (K := K) ρ R hρ hR
  rw [archimedeanBoxSingularIntegral_re k s hk ρ R hρ,
    smoothWeightedSingularIntegral_eq_density k s hk ρ R hρ hR,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sourceContinuousDensity_ge_box k s hk ρ R (ρ/2) (2*R) hρ (half_pos hρ)
    (smoothSourceMeasure_lower ρ R hρ hR) (smoothSourceMeasure_upper ρ R hρ hR) b

/-- One fixed explicit nonnegative smooth product weight, with compact
positive support separated from zero, works for every balanced target. -/
theorem exists_uniform_smooth_product_singularIntegral (k s : ℕ) (hk : 0 < k) :
    ∃ ρ R c δ : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧ 0 < δ ∧
      ContDiff ℝ ∞ (smoothRootWeight (K := K) ρ R) ∧
      HasCompactSupport (smoothRootWeight (K := K) ρ R) ∧
      (∀ x : mixedSpace K, 0 ≤ smoothRootWeight ρ R x ∧ smoothRootWeight ρ R x ≤ 1) ∧
      Function.support (smoothRootWeight (K := K) ρ R) ⊆ rootBox K (ρ/2) (2*R) ∧
      (∀ b : mixedSpace K, Integrable (fun β : mixedSpace K =>
        archimedeanTraceCharacter (-β) b * weightedRootIntegral k (smoothRootWeight ρ R) β ^ (s+2))) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        ∀ b ∈ Metric.ball (normalizedTarget k u ν) δ,
          c ≤ (weightedSingularIntegral k (s+2) (smoothRootWeight ρ R) b).re ∧
          (weightedSingularIntegral k (s+2) (smoothRootWeight ρ R) b).im = 0 := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, _, ht⟩ :=
    exists_uniform_normalized_target_singularIntegral (K := K) k s hk
  refine ⟨ρ, R, c, δ, hρ, hR, hc, hδ, smoothRootWeight_contDiff ρ R,
    smoothRootWeight_hasCompactSupport ρ R hρ hR,
    fun x => ⟨smoothRootWeight_nonneg ρ R x, smoothRootWeight_le_one ρ R x⟩,
    smoothRootWeight_support_subset ρ R hρ hR,
    smoothWeighted_phase_integrable k s hk ρ R hρ hR, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  refine ⟨u, hu, fun b hball => ⟨(hb b hball).1.trans
    (smoothWeightedSingularIntegral_ge_box k s hk ρ R hρ hR b), ?_⟩⟩
  rw [smoothWeightedSingularIntegral_eq_density k s hk ρ R hρ hR,
    Complex.smul_im, Complex.ofReal_im, smul_zero]

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.smoothWeightedSingularIntegral_eq_density
#print axioms WaringSiegel.WSL3.exists_uniform_smooth_product_singularIntegral
