import WaringSiegel.WSL3UnitPairedMeasures
import WaringSiegel.WSL3PoissonBasis

/-!
# The manuscript's integer-lattice normalization

The source Haar measure is normalized by the actual covolume of the integral
basis lattice. Its fundamental domain has measure one, and the paired trace
frequency measure has the determinant factor proved in the inversion theorem.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical
open NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3Poisson
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

def integerLatticeSourceScale (K : Type*) [Field K] [NumberField K] : ℝ :=
  (basisCovolume (mixedEmbedding.latticeBasis K))⁻¹

theorem integerLatticeSourceScale_pos : 0 < integerLatticeSourceScale K :=
  inv_pos.mpr (basisCovolume_pos (mixedEmbedding.latticeBasis K))

/-- This source measure is literally coordinate Lebesgue measure in an
integral basis, not an unspecified normalization constant. -/
theorem integerLatticeSourceMeasure_eq_map :
    archimedeanSourceMeasure (integerLatticeSourceScale K) =
      Measure.map (mixedEmbedding.latticeBasis K).equivFunL.symm volume := by
  exact (basis_map_volume (mixedEmbedding.latticeBasis K)).symm

/-- The actual integer-lattice fundamental domain has source volume one. -/
theorem integerLatticeSourceMeasure_fundamentalDomain :
    archimedeanSourceMeasure (integerLatticeSourceScale K)
      (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)) = 1 := by
  rw [integerLatticeSourceMeasure_eq_map]
  exact basis_map_volume_fundamentalDomain (mixedEmbedding.latticeBasis K)

/-- Exact singular-integral normalization in the manuscript's integral-basis
source coordinates and paired trace-dual frequency coordinates. -/
theorem latticeNormalizedBoxSingularIntegral_eq_density (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    pairedBoxSingularIntegral (integerLatticeSourceScale K) k (s+2) ρ R b =
      (integerLatticeSourceScale K)^(s+1) •
        (continuousArchimedeanDensity k s ρ R b : ℂ) :=
  pairedBoxSingularIntegral_eq_density _ integerLatticeSourceScale_pos k s hk ρ R hρ b

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.latticeNormalizedBoxSingularIntegral_eq_density
