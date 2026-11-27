import WaringSiegel.WSL2TraceHaar
import WaringSiegel.WSL2ArchimedeanTrace

/-!
# WSL2: Haar preservation under multiplication by an algebraic integer

The map is induced by actual multiplication in the mixed space. For every
nonzero algebraic integer it is continuous and onto, hence preserves the
probability Haar measure on the actual quotient trace torus.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem archInverseDifferent_mul_mem (a : 𝓞 K) {x : mixedSpace K}
    (hx : x ∈ archInverseDifferentLattice (K := K)) :
    mixedEmbedding K (a : K) * x ∈ archInverseDifferentLattice (K := K) := by
  obtain ⟨α, hα, rfl⟩ := (mem_archInverseDifferentLattice x).mp hx
  apply (mem_archInverseDifferentLattice _).mpr
  refine ⟨(a : K) * α, ?_, map_mul _ _ _⟩
  simpa only [Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] using
    (inverseDifferent K : Submodule (𝓞 K) K).smul_mem a hα

def traceTorusMul (a : 𝓞 K) : ArchimedeanTraceTorus K →+ ArchimedeanTraceTorus K :=
  ((archInverseDifferentLattice (K := K)).mapQ (archInverseDifferentLattice (K := K))
    ((LinearMap.mulLeft ℝ (mixedEmbedding K (a : K))).restrictScalars ℤ)
    (fun x hx => archInverseDifferent_mul_mem a hx)).toAddMonoidHom

theorem traceTorusMul_mk (a : 𝓞 K) (x : mixedSpace K) :
    traceTorusMul a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mixedEmbedding K (a : K) * x) := rfl

theorem traceTorusMul_continuous (a : 𝓞 K) : Continuous (traceTorusMul a) := by
  apply (QuotientAddGroup.isQuotientMap_mk (archInverseDifferentLattice (K := K)).toAddSubgroup).continuous_iff.mpr
  exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

theorem traceTorusMul_surjective (a : 𝓞 K) (ha : a ≠ 0) : Function.Surjective (traceTorusMul a) := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  refine ⟨Submodule.Quotient.mk (mixedEmbedding K ((a : K)⁻¹) * x), ?_⟩
  rw [traceTorusMul_mk, ← mul_assoc, ← map_mul]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  rw [mul_inv_cancel₀ haK, map_one, one_mul]
  rfl

theorem traceTorusMul_map_Haar (a : 𝓞 K) (ha : a ≠ 0) :
    Measure.map (traceTorusMul a) traceHaar = traceHaar := by
  have hf : Continuous (traceTorusMul a) := traceTorusMul_continuous a
  have hp : Tendsto (traceTorusMul a)
      (cocompact (ArchimedeanTraceTorus K)) (cocompact (ArchimedeanTraceTorus K)) := by
    rw [cocompact_eq_bot]
    exact tendsto_bot
  letI : IsAddHaarMeasure (Measure.map (traceTorusMul a) traceHaar) :=
    Measure.isAddHaarMeasure_map traceHaar (traceTorusMul a) hf (traceTorusMul_surjective a ha) hp
  letI : IsProbabilityMeasure (Measure.map (traceTorusMul a) traceHaar) :=
    Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem traceTorusMul_measurePreserving (a : 𝓞 K) (ha : a ≠ 0) :
    MeasurePreserving (traceTorusMul a) traceHaar traceHaar :=
  ⟨(traceTorusMul_continuous a).measurable, traceTorusMul_map_Haar a ha⟩

end WaringSiegel
