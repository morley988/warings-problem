import WaringSiegel.WSL4MixedCountEmbedding
import WaringSiegel.WSL4ArchMixedPointwise

/-! # Every half-box transformed solution contributes one to the actual smooth integral -/
noncomputable section
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem mixedBoxCount_le_nearZero_integral (H Z M Y : Finset (𝓞 K))
    (H₀ P₀ M₀ R₀ : ℝ) (hH₀ : 0 < H₀) (hP₀ : 0 < P₀)
    (hM₀ : 0 < M₀) (hR₀ : 0 < R₀)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ ‖mixedEmbedding K (h : K)‖ ≤ H₀/2)
    (hZ : ∀ z ∈ Z, ‖mixedEmbedding K (z : K)‖ ≤ P₀/2)
    (hM : ∀ m ∈ M, ‖mixedEmbedding K (m : K)‖ ≤ M₀/2)
    (hY : ∀ y ∈ Y, ‖mixedEmbedding K (y : K)‖ ≤ R₀/2) :
    (mixedBoxCount H Z M Y : ℝ) ≤
      (∫ q, nearZeroMixedSIntegrand (K:=K) H₀ P₀ M₀ R₀
        hH₀.ne' hP₀.ne' hM₀.ne' hR₀.ne' q ∂traceHaar).re := by
  rw [nearZeroMixedSIntegrand,compactMixedSIntegral_eq_weightedCount]
  · exact mixedBoxCount_le_compactWeightedCount H Z M Y H₀ P₀ M₀ R₀
      hH₀ hP₀ hM₀ hR₀ hH hZ hM hY
  all_goals exact nearZeroSchwartz_majorant.2.2.2.1

theorem mixedBoxCount_le_nearZero_integral_norm (H Z M Y : Finset (𝓞 K))
    (H₀ P₀ M₀ R₀ : ℝ) (hH₀ : 0 < H₀) (hP₀ : 0 < P₀)
    (hM₀ : 0 < M₀) (hR₀ : 0 < R₀)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ ‖mixedEmbedding K (h : K)‖ ≤ H₀/2)
    (hZ : ∀ z ∈ Z, ‖mixedEmbedding K (z : K)‖ ≤ P₀/2)
    (hM : ∀ m ∈ M, ‖mixedEmbedding K (m : K)‖ ≤ M₀/2)
    (hY : ∀ y ∈ Y, ‖mixedEmbedding K (y : K)‖ ≤ R₀/2) :
    (mixedBoxCount H Z M Y : ℝ) ≤
      ‖∫ q, nearZeroMixedSIntegrand (K:=K) H₀ P₀ M₀ R₀
        hH₀.ne' hP₀.ne' hM₀.ne' hR₀.ne' q ∂traceHaar‖ :=
  (mixedBoxCount_le_nearZero_integral H Z M Y H₀ P₀ M₀ R₀
    hH₀ hP₀ hM₀ hR₀ hH hZ hM hY).trans (Complex.re_le_norm _)

#print axioms mixedBoxCount_le_nearZero_integral
#print axioms mixedBoxCount_le_nearZero_integral_norm
end WaringSiegel.WSL4Local
