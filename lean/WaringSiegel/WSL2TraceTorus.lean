import WaringSiegel.WSL2ArchimedeanCoordinates
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# WSL2: the actual archimedean trace torus

The quotient of the mixed space by the embedded inverse different is
identified with the coordinate torus by a continuous additive equivalence.
The inverse-different lattice equality, compactness, and continuity are all
proved; the coordinate torus is not merely substituted as a formal model.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.mixedEmbedding Module Topology

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def archInverseDifferentLattice : Submodule ℤ (mixedSpace K) :=
  Submodule.span ℤ (Set.range (archimedeanTraceDualBasis (K := K)))

theorem archInverseDifferentLattice_eq_map :
    archInverseDifferentLattice (K := K) =
      Submodule.map (mixedEmbedding K).toIntAlgHom.toLinearMap
        ((inverseDifferent K : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  rw [← span_integralTraceDualBasis, Submodule.map_span, ← Set.range_comp]
  unfold archInverseDifferentLattice
  congr 1
  congr 1
  funext i
  exact archimedeanTraceDualBasis_apply i

theorem mem_archInverseDifferentLattice (x : mixedSpace K) :
    x ∈ archInverseDifferentLattice (K := K) ↔
      ∃ a : K, a ∈ inverseDifferent K ∧ mixedEmbedding K a = x := by
  rw [archInverseDifferentLattice_eq_map, Submodule.mem_map]
  rfl

def archimedeanTorusHom : mixedSpace K →+ (NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) where
  toFun x := fun i => ((archimedeanDualCoordinates x i : ℝ) : AddCircle (1 : ℝ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp only [map_add, Pi.add_apply, AddCircle.coe_add]

theorem archimedeanTorusHom_continuous : Continuous (archimedeanTorusHom (K := K)) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp (archimedeanDualCoordinates (K := K)).continuous)

theorem archimedeanTorusHom_surjective : Function.Surjective (archimedeanTorusHom (K := K)) := by
  intro θ
  choose x hx using fun i => Quotient.exists_rep (θ i)
  refine ⟨(archimedeanDualCoordinates (K := K)).symm x, ?_⟩
  ext i
  change (((archimedeanDualCoordinates ((archimedeanDualCoordinates (K := K)).symm x)) i : ℝ) :
    AddCircle (1 : ℝ)) = θ i
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hx i

theorem archimedeanTorusHom_ker :
    (archimedeanTorusHom (K := K)).ker = (archInverseDifferentLattice (K := K)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, funext_iff]
  change (∀ i, (((archimedeanTraceDualBasis (K := K)).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0) ↔ _
  rw [Submodule.mem_toAddSubgroup, archInverseDifferentLattice, Basis.mem_span_iff_repr_mem ℤ]
  simp only [AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]
  rfl

theorem archimedeanTorusHom_field (a : K) :
    archimedeanTorusHom (mixedEmbedding K a) = traceTorusPoint K a := by
  ext i
  exact congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) (archimedeanDualCoordinates_field a i)

abbrev ArchimedeanTraceTorus (K : Type*) [Field K] [NumberField K] :=
  mixedSpace K ⧸ archInverseDifferentLattice (K := K)

instance archimedeanTraceTorus_compactSpace : CompactSpace (ArchimedeanTraceTorus K) := by
  let b := archimedeanTraceDualBasis (K := K)
  have hb : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded
      isClosed_closure (ZSpan.fundamentalDomain_isBounded b).closure
  have himage : (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) ''
      closure (ZSpan.fundamentalDomain b) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    let y := ZSpan.quotientEquiv b q
    refine ⟨y, subset_closure y.property, ?_⟩
    have h := (ZSpan.quotientEquiv b).symm_apply_apply q
    simpa only [ZSpan.quotientEquiv.symm_apply] using h
  constructor
  rw [← himage]
  exact hb.image continuous_quotient_mk'

def archimedeanTraceTorusEquiv : ArchimedeanTraceTorus K ≃+
    (NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) :=
  (QuotientAddGroup.quotientAddEquivOfEq archimedeanTorusHom_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ archimedeanTorusHom_surjective)

theorem archimedeanTraceTorusEquiv_mk (x : mixedSpace K) :
    archimedeanTraceTorusEquiv (Submodule.Quotient.mk x) = archimedeanTorusHom x := by
  rfl

theorem archimedeanTraceTorusEquiv_continuous :
    Continuous (archimedeanTraceTorusEquiv (K := K)) := by
  apply (QuotientAddGroup.isQuotientMap_mk (archInverseDifferentLattice (K := K)).toAddSubgroup).continuous_iff.mpr
  exact archimedeanTorusHom_continuous

/-- The actual trace torus and the coordinate torus are homeomorphic via
the same additive equivalence used in Fourier coefficient extraction. -/
def archimedeanTraceTorusHomeomorph : ArchimedeanTraceTorus K ≃ₜ
    (NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) :=
  (archimedeanTraceTorusEquiv (K := K)).toEquiv.toHomeomorphOfContinuousClosed
    archimedeanTraceTorusEquiv_continuous archimedeanTraceTorusEquiv_continuous.isClosedMap

theorem archimedeanTraceTorusHomeomorph_mk (x : mixedSpace K) :
    archimedeanTraceTorusHomeomorph (Submodule.Quotient.mk x) = archimedeanTorusHom x :=
  archimedeanTraceTorusEquiv_mk x

end WaringSiegel
