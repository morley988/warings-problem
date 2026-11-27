import WaringSiegel.WSL2TraceTorus
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# WSL2: normalized Haar measure on the actual trace torus

The probability measure below is transported through the proved topological
group isomorphism. It is proved to be an additive Haar measure. All coordinate
integral identities therefore transfer to the actual quotient torus.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

instance archimedeanTraceTorus_measurableSpace : MeasurableSpace (ArchimedeanTraceTorus K) :=
  borel _

instance archimedeanTraceTorus_borelSpace : BorelSpace (ArchimedeanTraceTorus K) := ⟨rfl⟩

def archimedeanTraceTorusContinuousAddEquiv : ArchimedeanTraceTorus K ≃ₜ+
    (NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) where
  toAddEquiv := archimedeanTraceTorusEquiv
  continuous_toFun := archimedeanTraceTorusEquiv_continuous
  continuous_invFun := (archimedeanTraceTorusHomeomorph (K := K)).symm.continuous

def traceHaar : Measure (ArchimedeanTraceTorus K) :=
  Measure.map (archimedeanTraceTorusContinuousAddEquiv (K := K)).symm
    (latticeHaar (ι := NumberFieldCoordinateIndex K))

instance latticeHaar_probability_measure {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

instance latticeHaar_addHaar_measure {ι : Type*} [Fintype ι] :
    IsAddHaarMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

instance traceHaar_isProbabilityMeasure : IsProbabilityMeasure (traceHaar (K := K)) :=
  Measure.isProbabilityMeasure_map
    (archimedeanTraceTorusContinuousAddEquiv (K := K)).symm.continuous.measurable.aemeasurable

instance traceHaar_isAddHaarMeasure : IsAddHaarMeasure (traceHaar (K := K)) := by
  unfold traceHaar
  infer_instance

theorem traceHaar_map_coordinates :
    Measure.map (archimedeanTraceTorusContinuousAddEquiv (K := K)) traceHaar = latticeHaar := by
  have hf : Measurable (archimedeanTraceTorusContinuousAddEquiv (K := K)) :=
    (archimedeanTraceTorusContinuousAddEquiv (K := K)).continuous.measurable
  have hg : Measurable (archimedeanTraceTorusContinuousAddEquiv (K := K)).symm :=
    (archimedeanTraceTorusContinuousAddEquiv (K := K)).symm.continuous.measurable
  rw [traceHaar, Measure.map_map hf hg]
  simp only [Function.comp_def, ContinuousAddEquiv.apply_symm_apply]
  exact Measure.map_id

theorem traceHaar_coordinates_measurePreserving :
    MeasurePreserving (archimedeanTraceTorusContinuousAddEquiv (K := K)) traceHaar latticeHaar :=
  ⟨(archimedeanTraceTorusContinuousAddEquiv (K := K)).continuous.measurable,
    traceHaar_map_coordinates⟩

/-- Change of variables is valid for every Bochner-integral integrand, with
the ordinary mathlib convention for nonintegrable functions. -/
theorem traceHaar_integral_coordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) → E) :
    (∫ q, f (archimedeanTraceTorusContinuousAddEquiv q) ∂traceHaar) =
      ∫ θ, f θ ∂latticeHaar :=
  traceHaar_coordinates_measurePreserving.integral_comp
    (archimedeanTraceTorusHomeomorph (K := K)).toMeasurableEquiv.measurableEmbedding f

def traceTorusCharacter (a : 𝓞 K) (q : ArchimedeanTraceTorus K) : ℂ :=
  latticeCharacter (integerCoordinates K a) (archimedeanTraceTorusContinuousAddEquiv q)

theorem traceTorusCharacter_integral (a : 𝓞 K) :
    (∫ q, traceTorusCharacter a q ∂traceHaar) = if a = 0 then 1 else 0 := by
  change (∫ q, latticeCharacter (integerCoordinates K a)
    (archimedeanTraceTorusContinuousAddEquiv q) ∂traceHaar) = _
  rw [traceHaar_integral_coordinates, latticeCharacter_orthogonality]
  simp only [map_eq_zero_iff _ (integerCoordinates_injective K)]

end WaringSiegel
