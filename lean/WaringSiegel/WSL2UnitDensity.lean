import WaringSiegel.WSL2UnitAbsoluteContinuity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Genuine archimedean Waring densities and uniform positivity

The actual sum-of-powers pushforward has finite mass and is absolutely
continuous. Its Radon–Nikodym density is therefore a genuine integrable
Lebesgue density. The proved Jacobian/compactness volume bound gives one
strictly positive lower bound almost everywhere near every normalized target.
The Fourier inversion identification is not asserted here.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option synthInstance.maxHeartbeats 100000

instance archimedeanWaringMeasure_finite (k s : ℕ) (ρ R : ℝ) :
    IsFiniteMeasure (archimedeanWaringMeasure (K := K) k s ρ R) := by
  letI : IsFiniteMeasureOnCompacts (volume : Measure (Fin s → mixedSpace K)) := by
    change IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.isFiniteMeasureOnCompacts _
  letI : IsFiniteMeasure (volume.restrict (rootTupleBox (K := K) s ρ R)) :=
    isFiniteMeasure_restrict.mpr (rootTupleBox_isCompact (K := K) s ρ R).measure_lt_top.ne
  unfold archimedeanWaringMeasure
  infer_instance

/-- The density of the actual full sum-of-powers image measure. -/
def archimedeanWaringDensity (k s : ℕ) (ρ R : ℝ) : mixedSpace K → ENNReal :=
  (archimedeanWaringMeasure (K := K) k s ρ R).rnDeriv volume

theorem archimedeanWaringDensity_measurable (k s : ℕ) (ρ R : ℝ) :
    Measurable (archimedeanWaringDensity (K := K) k s ρ R) := Measure.measurable_rnDeriv _ _

/-- This density reconstructs the actual measure, rather than merely naming
an arbitrary measurable function. -/
theorem archimedeanWaringDensity_measure (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    volume.withDensity (archimedeanWaringDensity (K := K) k s ρ R) =
      archimedeanWaringMeasure k s ρ R :=
  Measure.withDensity_rnDeriv_eq _ _
    (archimedeanWaringMeasure_absolutelyContinuous (K := K) k s hk ρ R hρ)

theorem archimedeanWaringDensity_finite_ae (k s : ℕ) (ρ R : ℝ) :
    ∀ᵐ x ∂(volume : Measure (mixedSpace K)), archimedeanWaringDensity k s ρ R x < ⊤ :=
  Measure.rnDeriv_lt_top _ _

theorem archimedeanWaringDensity_integrable (k s : ℕ) (ρ R : ℝ) :
    Integrable (fun x : mixedSpace K => (archimedeanWaringDensity k s ρ R x).toReal) := by
  apply integrableOn_univ.mp
  exact Measure.integrableOn_toReal_rnDeriv
    (measure_lt_top (archimedeanWaringMeasure (K := K) k s ρ R) Set.univ).ne

/-- A measure lower bound gives an actual almost-everywhere density lower
bound. This follows by comparison of integrals on measurable subsets. -/
theorem ae_density_lower_of_measure_domination {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (f : E → ENNReal) (hf : Measurable f)
    (c : ENNReal) {V : Set E} (hV : MeasurableSet V)
    (h : c • μ.restrict V ≤ μ.withDensity f) :
    ∀ᵐ x ∂μ.restrict V, c ≤ f x := by
  have hglobal : V.indicator (fun _ => c) ≤ᵐ[μ] f := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_const.indicator hV)
    intro A hA _
    rw [← withDensity_apply _ hA, ← withDensity_apply _ hA,
      withDensity_indicator hV, withDensity_const]
    exact Measure.le_iff.mp h A hA
  filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem hV] with x hx hxV
  simpa only [Set.indicator_of_mem hxV] using hx

/-- Uniform actual density positivity on a neighborhood of every compact
normalized target. The positive constant and the positive compact root box
are chosen before the target. The lower bound is a.e.; no pointwise choice
of the Radon–Nikodym representative is imposed. -/
theorem exists_uniform_archimedean_density_lower (k s : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ IsCompact (rootBox K ρ R) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ b ∈ compactTargetSet K B,
        ∃ V : Set (mixedSpace K), IsOpen V ∧ b ∈ V ∧
          ∀ᵐ x ∂volume.restrict V, c ≤ (archimedeanWaringDensity k s ρ R x).toReal := by
  obtain ⟨ρ, R, hρ, hR, hcompact, c, hc, hcfin, hlocal⟩ :=
    exists_uniform_archimedean_volume_lower (K := K) k s hk B hB
  refine ⟨ρ, R, hρ, hR, hcompact, c.toReal, ENNReal.toReal_pos hc.ne' hcfin.ne, ?_⟩
  intro b hb
  obtain ⟨V, hV, hbV, hdom⟩ := hlocal b hb
  rw [← archimedeanWaringDensity_measure k s hk ρ R hρ] at hdom
  have hae := ae_density_lower_of_measure_domination volume
    (archimedeanWaringDensity (K := K) k s ρ R)
    (archimedeanWaringDensity_measurable k s ρ R) c hV.measurableSet hdom
  refine ⟨V, hV, hbV, ?_⟩
  filter_upwards [hae, ae_restrict_of_ae (archimedeanWaringDensity_finite_ae (K := K) k s ρ R)]
    with x hx hxfin
  exact ENNReal.toReal_mono hxfin.ne hx

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.archimedeanWaringDensity_measure
#print axioms WaringSiegel.WSL2.exists_uniform_archimedean_density_lower
