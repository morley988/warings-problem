import WaringSiegel.WSL3UnitTraceInversion
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Source measures and genuine weighted Waring densities

A source measure is transported by the literal power map and convolved.
This abstraction permits smooth cutoff sources to be compared to the already
verified inner and outer boxes without changing either source profile.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

/-- Product measures preserve measure domination. -/
theorem measure_prod_mono {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ₁ μ₂ : Measure X} {ν₁ ν₂ : Measure Y} [SFinite ν₁] [SFinite ν₂]
    (hμ : μ₁ ≤ μ₂) (hν : ν₁ ≤ ν₂) : μ₁.prod ν₁ ≤ μ₂.prod ν₂ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.prod_apply hA, Measure.prod_apply hA]
  exact lintegral_mono' hμ (fun _ => hν _)

/-- Convolution preserves measure domination in both arguments. -/
theorem measure_conv_mono {μ₁ μ₂ ν₁ ν₂ : Measure (mixedSpace K)}
    [SFinite ν₁] [SFinite ν₂] (hμ : μ₁ ≤ μ₂) (hν : ν₁ ≤ ν₂) :
    μ₁.conv ν₁ ≤ μ₂.conv ν₂ :=
  Measure.map_mono (measure_prod_mono hμ hν) measurable_add

/-- The distribution of s+1 independent literal k-th powers drawn from μ. -/
def sourceWaringMeasure (k : ℕ) (μ : Measure (mixedSpace K)) : ℕ → Measure (mixedSpace K)
  | 0 => Measure.map (fun x : mixedSpace K => x^k) μ
  | s+1 => (Measure.map (fun x : mixedSpace K => x^k) μ).conv (sourceWaringMeasure k μ s)

instance sourceWaringMeasure_finite (k s : ℕ) (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (sourceWaringMeasure k μ s) := by
  induction s with
  | zero => dsimp only [sourceWaringMeasure]; infer_instance
  | succ s ih =>
      letI := ih
      change IsFiniteMeasure ((Measure.map (fun x : mixedSpace K => x^k) μ).conv
        (sourceWaringMeasure k μ s))
      infer_instance

/-- The abstraction agrees exactly with the original literal box pushforward. -/
theorem sourceWaringMeasure_box (k s : ℕ) (ρ R : ℝ) :
    sourceWaringMeasure (K := K) k (volume.restrict (rootBox K ρ R)) s =
      archimedeanWaringMeasure k s ρ R := by
  induction s with
  | zero => exact (archimedeanWaringMeasure_zero k ρ R).symm
  | succ s ih =>
      rw [sourceWaringMeasure, ih,
        ← archimedeanWaringMeasure_zero (K := K), ← archimedeanWaringMeasure_succ]

theorem sourceWaringMeasure_mono (k s : ℕ) {μ ν : Measure (mixedSpace K)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≤ ν) :
    sourceWaringMeasure k μ s ≤ sourceWaringMeasure k ν s := by
  have hzero : sourceWaringMeasure k μ 0 ≤ sourceWaringMeasure k ν 0 :=
    Measure.map_mono h (continuous_id.pow k).measurable
  induction s with
  | zero => exact hzero
  | succ s ih => exact measure_conv_mono hzero ih

/-- This is the actual density of the weighted image measure. -/
def sourceWaringDensity (k s : ℕ) (μ : Measure (mixedSpace K)) : mixedSpace K → ENNReal :=
  (sourceWaringMeasure k μ s).rnDeriv volume

theorem sourceWaringDensity_measurable (k s : ℕ) (μ : Measure (mixedSpace K)) :
    Measurable (sourceWaringDensity k s μ) := Measure.measurable_rnDeriv _ _

theorem sourceWaringDensity_finite_ae (k s : ℕ) (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ] :
    ∀ᵐ x ∂volume, sourceWaringDensity k s μ x < ⊤ := Measure.rnDeriv_lt_top _ _

theorem sourceWaringDensity_integrable (k s : ℕ) (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ] :
    Integrable (fun x => (sourceWaringDensity k s μ x).toReal) := by
  apply integrableOn_univ.mp
  exact Measure.integrableOn_toReal_rnDeriv (measure_lt_top (sourceWaringMeasure k μ s) Set.univ).ne

theorem sourceWaringMeasure_absolutelyContinuous (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R)) :
    sourceWaringMeasure k μ s ≪ volume := by
  letI : IsFiniteMeasure (volume.restrict (rootBox K ρ R)) :=
    isFiniteMeasure_restrict.mpr (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  have h := sourceWaringMeasure_mono k s hμ
  rw [sourceWaringMeasure_box] at h
  exact h.absolutelyContinuous.trans (archimedeanWaringMeasure_absolutelyContinuous k s hk ρ R hρ)

theorem sourceWaringDensity_measure (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R)) :
    volume.withDensity (sourceWaringDensity k s μ) = sourceWaringMeasure k μ s :=
  Measure.withDensity_rnDeriv_eq _ _ (sourceWaringMeasure_absolutelyContinuous k s hk ρ R hρ hμ)

/-- Measure domination becomes an actual almost-everywhere density comparison. -/
theorem rnDeriv_mono_of_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    {μ ν m : Measure X} [SigmaFinite m] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ m) (hν : ν ≪ m) (h : μ ≤ ν) : μ.rnDeriv m ≤ᵐ[m] ν.rnDeriv m := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
  intro A hA _
  rw [← withDensity_apply _ hA, ← withDensity_apply _ hA,
    Measure.withDensity_rnDeriv_eq _ _ hμ, Measure.withDensity_rnDeriv_eq _ _ hν]
  exact Measure.le_iff.mp h A hA

/-- The original box L² bound controls every source dominated by that box. -/
theorem sourceWaringDensity_memLp_two (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R)) :
    MemLp (fun x => (sourceWaringDensity k s μ x).toReal) 2 := by
  letI : IsFiniteMeasure (volume.restrict (rootBox K ρ R)) :=
    isFiniteMeasure_restrict.mpr (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  have hle := sourceWaringMeasure_mono k s hμ
  rw [sourceWaringMeasure_box] at hle
  have hden := rnDeriv_mono_of_absolutelyContinuous
    (sourceWaringMeasure_absolutelyContinuous k s hk ρ R hρ hμ)
    (archimedeanWaringMeasure_absolutelyContinuous k s hk ρ R hρ) hle
  apply (archimedeanWaringDensity_memLp_two k s hk ρ R hρ).mono'
    (sourceWaringDensity_measurable k s μ).ennreal_toReal.aestronglyMeasurable
  filter_upwards [hden, archimedeanWaringDensity_finite_ae (K := K) k s ρ R] with x hx hxfin
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hxfin.ne hx

end WaringSiegel.WSL3
