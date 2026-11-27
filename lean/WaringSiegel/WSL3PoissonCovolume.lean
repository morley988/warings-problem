import WaringSiegel.WSL3PoissonBasis
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Geometric covolumes under basis changes and products

These are identities for the measured fundamental parallelepipeds used in
Poisson summation. They keep determinant and product factors explicit.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Module Topology
open scoped BigOperators Classical
namespace WaringSiegel.WSL3Poisson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- Agreement with mathlib's covolume of the actual integer span. -/
theorem basisCovolume_eq_latticeCovolume (b : Basis ι ℝ E) :
    basisCovolume b = ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  exact (ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume)).symm

/-- The determinant is the geometric covolume multiplier. -/
theorem basisCovolume_map (b : Basis ι ℝ E) (A : E ≃L[ℝ] E) :
    basisCovolume (b.map A.toLinearEquiv) =
      |LinearMap.det A.toLinearMap| * basisCovolume b := by
  unfold basisCovolume
  rw [ZSpan.measureReal_fundamentalDomain (b.map A.toLinearEquiv) volume b]
  congr 2
  change b.det (A.toLinearMap ∘ b) = LinearMap.det A.toLinearMap
  rw [Basis.det_comp, Basis.det_self, mul_one]

/-- A measure-preserving coordinate equivalence preserves actual covolume. -/
theorem basisCovolume_map_measurePreserving
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasureSpace F] [BorelSpace F] [IsAddHaarMeasure (volume : Measure F)]
    (b : Basis ι ℝ E) (A : E ≃L[ℝ] F) (hA : MeasurePreserving A volume volume) :
    basisCovolume (b.map A.toLinearEquiv) = basisCovolume b := by
  unfold basisCovolume
  rw [← ZSpan.map_fundamentalDomain b A.toLinearEquiv]
  have hm : MeasurePreserving A.toHomeomorph.toMeasurableEquiv volume volume := hA
  have hset : A '' ZSpan.fundamentalDomain b = A.symm ⁻¹' ZSpan.fundamentalDomain b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
    · intro hy
      exact ⟨A.symm y, hy, A.apply_symm_apply y⟩
  rw [show (A.toLinearEquiv : E → F) = A from rfl, hset]
  exact hm.symm.measureReal_preimage (ZSpan.fundamentalDomain_measurableSet b).nullMeasurableSet

/-- The half-open parallelepiped of the product basis is a genuine product set. -/
theorem fundamentalDomain_prod
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    ZSpan.fundamentalDomain (b.prod c) =
      ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Sum.forall, Basis.prod_repr_inl, Basis.prod_repr_inr, Set.mem_prod]

/-- Covolume multiplies under direct products. -/
theorem basisCovolume_prod
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasureSpace F] [BorelSpace F] [IsAddHaarMeasure (volume : Measure F)]
    (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    basisCovolume (b.prod c) = basisCovolume b * basisCovolume c := by
  unfold basisCovolume
  rw [fundamentalDomain_prod]
  exact measureReal_prod_prod _ _

end WaringSiegel.WSL3Poisson
