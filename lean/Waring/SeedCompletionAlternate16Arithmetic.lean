import Waring.SeedCompletionHigher16SimpleSeeds
import Waring.SeedCompletionPaddedGeneralPower
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological
import Waring.SeedCompletionAlternate8Data
import Waring.CertificateInterpolation

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate16Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem alternate_total_snoc {j : ℕ} (φ : Fin j → ℝ) (ψ : ℝ) :
    total (Fin.snoc φ ψ)=total φ+ψ := Fin.sum_snoc ψ φ

theorem alternate_bounds_snoc {j : ℕ} (φ : Fin j → ℝ) (ψ : ℝ)
    (hφ : ∀ i,0≤φ i ∧ φ i≤1 ∧ 0≤shiftExponents 16 φ i)
    (hψ : 0≤ψ ∧ ψ≤1 ∧ 0≤1-(16:ℝ)*ψ) :
    ∀ i : Fin (j+1),0≤Fin.snoc (α := fun _ => ℝ) φ ψ i ∧ Fin.snoc (α := fun _ => ℝ) φ ψ i≤1 ∧
      0≤shiftExponents 16 (Fin.snoc φ ψ) i := by
  rw [Fin.forall_iff_castSucc]
  constructor
  · simpa only [shiftExponents,Fin.snoc_last] using hψ
  · intro i
    simpa only [shiftExponents,Fin.snoc_castSucc] using hφ i

end Waring.SeedCompletionAlternate16Seeds
