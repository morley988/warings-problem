import WaringSiegel.WSL4ArchPoisson
import WaringSiegel.WSL3IdealPoissonCubicDecay

/-! # Actual near-zero Fourier factors in the summable ideal-lattice kernel -/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [NumberField K]

theorem scaledNearZeroCubicFourier_lattice_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 0 < P), ∀ θ : mixedSpace K, ∀ ξ : K,
      ‖traceFourier (scaledNearZeroPowerSchwartz 3 P hP.ne' θ) (mixedEmbedding K ξ)‖ ≤
        (C*P^(finrank ℚ K)/cubicProductFrequencyWeight (1/3) (P^3 • θ)) *
          latticeProductDecay (cubicDualRadius (1/2) P θ) 0 ξ := by
  let N := finrank ℚ K+2
  obtain ⟨C,hC,hb⟩ := scaledNearZeroCubicFourier_stationary_tail (K:=K) N
  let A : ℝ := (2^N)^(Fintype.card (InfinitePlace K))
  have hA : 0 < A := by unfold A; positivity
  refine ⟨C*A,mul_pos hC hA,fun P hP θ ξ => ?_⟩
  have ht := cubicProductTailWeight_inv_le (1/2) N (P^3 • θ) (-(P • mixedEmbedding K ξ))
  rw [cubicDualRadius_kernel (1/2) P hP θ ξ] at ht
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ C*P^(finrank ℚ K)/cubicProductFrequencyWeight (1/3) (P^3 • θ) from
      div_nonneg (mul_nonneg hC.le (pow_nonneg hP.le _)) (cubicProductFrequencyWeight_pos (1/3) _).le)
  calc
    _ ≤ C*P^(finrank ℚ K)/(cubicProductFrequencyWeight (1/3) (P^3 • θ)*
        cubicProductTailWeight (1/2) N (P^3 • θ) (-(P • mixedEmbedding K ξ))) := hb P hP θ (mixedEmbedding K ξ)
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,mul_inv,one_mul,A,mul_assoc,mul_left_comm,mul_comm] using hm

#print axioms scaledNearZeroCubicFourier_lattice_decay
end WaringSiegel.WSL4
