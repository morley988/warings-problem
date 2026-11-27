import WaringSiegel.WSL3PoissonCovolume
import WaringSiegel.WSL3PoissonTrace
import WaringSiegel.WSL2Conductor
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Exact covolumes of the actual integer and inverse-different lattices

These are geometric covolumes in standard mixed-space volume. Their product
retains the factor `4⁻ʳ²` from the actual trace form at complex places.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem integer_basisCovolume :
    basisCovolume (NumberField.mixedEmbedding.latticeBasis K) =
      (2⁻¹:ℝ)^nrComplexPlaces K * Real.sqrt |(NumberField.discr K:ℝ)| := by
  rw [basisCovolume_eq_latticeCovolume, NumberField.mixedEmbedding.span_latticeBasis,
    NumberField.mixedEmbedding.covolume_integerLattice]

theorem inverseDifferent_absNorm :
    (FractionalIdeal.absNorm (inverseDifferent K):ℝ) = |(NumberField.discr K:ℝ)|⁻¹ := by
  rw [inverseDifferent, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal (K:=K)]
  push_cast
  simp only [Int.cast_natAbs, Int.cast_abs]

theorem inverseDifferent_basisCovolume :
    basisCovolume (archimedeanTraceDualBasis (K:=K)) =
      |(NumberField.discr K:ℝ)|⁻¹ * (2⁻¹:ℝ)^nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K:ℝ)| := by
  let I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (inverseDifferent K) (inverseDifferent_ne_zero (K:=K))
  have h : Submodule.span ℤ (Set.range (archimedeanTraceDualBasis (K:=K))) =
      NumberField.mixedEmbedding.idealLattice K I := by
    ext x
    change x ∈ archInverseDifferentLattice (K:=K) ↔ _
    rw [mem_archInverseDifferentLattice, NumberField.mixedEmbedding.mem_idealLattice]
    rfl
  rw [basisCovolume_eq_latticeCovolume, h,
    NumberField.mixedEmbedding.covolume_idealLattice]
  change (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*
    (2⁻¹:ℝ)^nrComplexPlaces K * Real.sqrt |(NumberField.discr K:ℝ)| = _
  rw [inverseDifferent_absNorm]

/-- The actual trace-dual lattice covolumes multiply to `4⁻ʳ²`. -/
theorem trace_lattice_covolume_product :
    basisCovolume (NumberField.mixedEmbedding.latticeBasis K) *
      basisCovolume (archimedeanTraceDualBasis (K:=K)) =
        ((4:ℝ)^nrComplexPlaces K)⁻¹ := by
  rw [integer_basisCovolume, inverseDifferent_basisCovolume]
  have hd : |(NumberField.discr K:ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hs := Real.sq_sqrt (abs_nonneg (NumberField.discr K:ℝ))
  calc
    _ = ((2⁻¹:ℝ)^nrComplexPlaces K)^2 *
        (|(NumberField.discr K:ℝ)|⁻¹ * (Real.sqrt |(NumberField.discr K:ℝ)|)^2) := by ring
    _ = ((2⁻¹:ℝ)^nrComplexPlaces K)^2 := by rw [hs, inv_mul_cancel₀ hd, mul_one]
    _ = _ := by rw [← pow_mul, mul_comm (nrComplexPlaces K) 2, pow_mul]; norm_num [← inv_pow]

end WaringSiegel.WSL3Poisson
