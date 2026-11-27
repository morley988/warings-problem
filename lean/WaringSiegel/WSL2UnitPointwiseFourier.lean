import WaringSiegel.WSL2UnitContinuousDensity
import WaringSiegel.WSL2UnitFourier

/-!
# Compact continuous archimedean densities and their actual Fourier transform

The continuous representative reconstructs the literal image measure, has
compact support, and has the same proved forward trace-transform identity.
Fourier inversion and absolute frequency integrability remain separate goals.
-/
noncomputable section
open MeasureTheory
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
local instance : BorelSpace (mixedSpace K) := inferInstance

/-- The continuous representative is genuinely integrable. -/
theorem continuousArchimedeanDensity_integrable (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Integrable (continuousArchimedeanDensity (K := K) k s ρ R) :=
  (archimedeanWaringDensity_integrable k (s+1) ρ R).congr
    (continuousArchimedeanDensity_ae_eq k s hk ρ R hρ)

/-- Exact forward transform for the continuous actual density of s+2 roots. -/
theorem continuousArchimedeanDensity_fourier (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (β : mixedSpace K) :
    (∫ b, continuousArchimedeanDensity k s ρ R b • archimedeanTraceCharacter β b) =
      archimedeanRootIntegral k ρ R β ^ (s+2) := by
  calc
    _ = ∫ b, (archimedeanWaringDensity k (s+1) ρ R b).toReal •
        archimedeanTraceCharacter β b := by
      apply integral_congr_ae
      filter_upwards [continuousArchimedeanDensity_ae_eq k s hk ρ R hρ] with x hx
      rw [hx]
    _ = _ := archimedeanWaringDensity_fourier k (s+1) hk ρ R hρ β

/-- The continuous density vanishes off the actual compact image of its
root box. In particular its support is compact, without a support assumption. -/
theorem continuousArchimedeanDensity_hasCompactSupport (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (continuousArchimedeanDensity (K := K) k s ρ R) := by
  let D := rootTupleBox (K := K) (s+1) ρ R
  let F := archimedeanWaringMap (K := K) k (s+1)
  let C := F '' D
  let f := continuousArchimedeanDensity (K := K) k s ρ R
  have hF : Continuous F := by
    change Continuous (fun x : ArchimedeanTupleSpace K (s+1) => x.1^k + ∑ i, (x.2 i)^k)
    fun_prop
  have hC : IsCompact C := (rootTupleBox_isCompact (K := K) (s+1) ρ R).image hF
  have hf : Continuous f := continuousArchimedeanDensity_continuous k s hk ρ R hρ
  have hz : (archimedeanWaringMeasure (K := K) k (s+1) ρ R) Cᶜ = 0 := by
    rw [archimedeanWaringMeasure, Measure.map_apply hF.measurable hC.isClosed.measurableSet.compl,
      Measure.restrict_apply (hF.measurable hC.isClosed.measurableSet.compl)]
    have he : F ⁻¹' Cᶜ ∩ D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (Set.mem_image_of_mem F hx.2)
    change volume (F ⁻¹' Cᶜ ∩ D) = 0
    rw [he, measure_empty]
  rw [← continuousArchimedeanDensity_measure k s hk ρ R hρ] at hz
  have hn : volume ({x | ENNReal.ofReal (f x) ≠ 0} ∩ Cᶜ) = 0 :=
    (withDensity_apply_eq_zero hf.measurable.ennreal_ofReal).mp hz
  have ho : IsOpen ({x | ENNReal.ofReal (f x) ≠ 0} ∩ Cᶜ) :=
    (isOpen_ne.preimage (ENNReal.continuous_ofReal.comp hf)).inter hC.isClosed.isOpen_compl
  have hempty := ho.eq_empty_of_measure_zero hn
  apply HasCompactSupport.of_support_subset_isCompact hC
  intro x hx
  by_contra hxC
  have hfx : ENNReal.ofReal (f x) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (lt_of_le_of_ne (continuousArchimedeanDensity_nonneg k s ρ R x)
      (Ne.symm hx))
  have hm : x ∈ {x | ENNReal.ofReal (f x) ≠ 0} ∩ Cᶜ := ⟨hfx, hxC⟩
  rw [hempty] at hm
  exact hm

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.continuousArchimedeanDensity_fourier
#print axioms WaringSiegel.WSL2.continuousArchimedeanDensity_hasCompactSupport
