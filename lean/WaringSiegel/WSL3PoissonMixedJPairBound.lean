import WaringSiegel.WSL3PoissonMixedJIntegral
import WaringSiegel.WSL3PoissonMixedPairCount

/-! # Literal diagonal/off-diagonal separation in the actual J integral -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- A concrete finite pair reduction, with zero and nonzero sixth-power
differences distinguished before applying their respective bounds. -/
theorem compactMixedJIntegral_pair_cost_bound (u w v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (W A B : ℝ) (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x, ‖w x‖ ≤ W)
    (hzero : mixedKIntegral u v huc hvc H R hH hR 0 ≤ A)
    (hoff : ∀ d : 𝓞 K, d ≠ 0 → mixedKIntegral u v huc hvc H R hH hR d ≤ B) :
    ‖compactMixedJIntegral u w v huc hwc hvc H M R hH hM hR‖ ≤
      W^2*(6*((compactIntegerSupport w hwc M hM).card:ℝ)*A+
        ((compactIntegerSupport w hwc M hM).card:ℝ)^2*B) := by
  let S := compactIntegerSupport w hwc M hM
  let F : 𝓞 K → ℝ := mixedKIntegral u v huc hvc H R hH hR
  have hF (d : 𝓞 K) : 0 ≤ F d := mixedKIntegral_nonneg _ _ _ _ _ _ _ _ _
  have hpair := power_pair_cost_bound (fun m : S => (m:𝓞 K)) Subtype.val_injective
    6 (by norm_num) F A B hA hB hzero hoff
  have hcard : Fintype.card S = S.card := Fintype.card_coe S
  rw [hcard] at hpair
  calc
    _ ≤ ∑ p : S × S,
        (‖w (M⁻¹ • mixedEmbedding K ((p.1:𝓞 K):K))‖*
          ‖w (M⁻¹ • mixedEmbedding K ((p.2:𝓞 K):K))‖)*F ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) :=
      compactMixedJIntegral_le_pairK _ _ _ _ _ _ _ _ _ _ _ _
    _ ≤ ∑ p : S × S, W^2*F ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (hF _)
      simpa only [pow_two] using mul_le_mul (hw _) (hw _) (norm_nonneg _) hW
    _ = W^2 * ∑ p : S × S, F ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hpair (sq_nonneg W)

end WaringSiegel.WSL3Poisson
