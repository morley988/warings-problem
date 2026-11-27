import Waring.SeedCompletionHigher9SimpleSeeds
import Waring.SeedCompletionPaddedGeneralPower
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological
import Waring.SeedCompletionAlternate9Data
import Waring.CertificateInterpolation

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem alternate_total_snoc {j : ℕ} (φ : Fin j → ℝ) (ψ : ℝ) :
    total (Fin.snoc φ ψ)=total φ+ψ := Fin.sum_snoc ψ φ

theorem alternate_bounds_snoc {j : ℕ} (φ : Fin j → ℝ) (ψ : ℝ)
    (hφ : ∀ i,0≤φ i ∧ φ i≤1 ∧ 0≤shiftExponents 9 φ i)
    (hψ : 0≤ψ ∧ ψ≤1 ∧ 0≤1-(9:ℝ)*ψ) :
    ∀ i : Fin (j+1),0≤Fin.snoc (α := fun _ => ℝ) φ ψ i ∧ Fin.snoc (α := fun _ => ℝ) φ ψ i≤1 ∧
      0≤shiftExponents 9 (Fin.snoc φ ψ) i := by
  rw [Fin.forall_iff_castSucc]
  constructor
  · simpa only [shiftExponents,Fin.snoc_last] using hψ
  · intro i
    simpa only [shiftExponents,Fin.snoc_castSucc] using hφ i

end Waring.SeedCompletionAlternate9Seeds
