import WaringSiegel.WSL3IdealPoissonCubic
import WaringSiegel.WSL2MomentLatticeProductDecay

/-!
# Actual cubic Fourier decay in the anisotropic ideal-lattice kernel

The uniform stationary estimate is compared to the literal summable product
kernel. Local radii depend on one plus the local power frequency, so all
archimedean aspect ratios are retained.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [NumberField K]

theorem cubicTailWeight_inv_le_product (R : ℝ) (N : ℕ) {t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    1/cubicTailWeight R N t u ≤
      2^N/(1+u/(cubicTailThreshold R*(1+t)))^N := by
  have hB := cubicTailThreshold_ge_one R
  have hA : 1 ≤ cubicTailThreshold R*(1+t) := by nlinarith
  have hAp : 0 < cubicTailThreshold R*(1+t) := lt_of_lt_of_le zero_lt_one hA
  have hp : 0 < (1+u/(cubicTailThreshold R*(1+t)))^N := by positivity
  apply (div_le_div_iff₀ (cubicTailWeight_pos R N t hu) hp).mpr
  rw [one_mul]
  by_cases hreg : cubicTailThreshold R*(1+t) ≤ u
  · rw [cubicTailWeight,if_pos hreg]
    have hdiv : u/(cubicTailThreshold R*(1+t)) ≤ u := div_le_self hu hA
    calc
      _ ≤ (1+u)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2^N*(1+u)^N := le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  · rw [cubicTailWeight,if_neg hreg,mul_one]
    have hdiv : u/(cubicTailThreshold R*(1+t)) ≤ 1 :=
      (div_le_one hAp).mpr (le_of_lt (lt_of_not_ge hreg))
    exact pow_le_pow_left₀ (by positivity) (by linarith) N

theorem cubicProductTailWeight_eq_places (R : ℝ) (N : ℕ) (θ u : mixedSpace K) :
    cubicProductTailWeight R N θ u =
      ∏ w : InfinitePlace K, cubicTailWeight (2*R) N (normAtPlace w θ) (normAtPlace w u) := by
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  unfold cubicProductTailWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isReal w.property,normAtPlace_apply_of_isReal w.property,
      Real.norm_eq_abs,Real.norm_eq_abs]
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isComplex w.property,normAtPlace_apply_of_isComplex w.property]

/-- Local radius in the unscaled linear variable. -/
def cubicLinearRadius (R : ℝ) (θ : mixedSpace K) (w : InfinitePlace K) : ℝ :=
  cubicTailThreshold (2*R)*(1+normAtPlace w θ)

theorem cubicLinearRadius_pos (R : ℝ) (θ : mixedSpace K) (w : InfinitePlace K) :
    0 < cubicLinearRadius R θ w := by
  have hB := cubicTailThreshold_ge_one (2*R)
  have hn := normAtPlace_nonneg w θ
  unfold cubicLinearRadius
  positivity

/-- Local radius in the actual ideal-dual variable ξ. -/
def cubicDualRadius (R P : ℝ) (θ : mixedSpace K) (w : InfinitePlace K) : ℝ :=
  cubicLinearRadius R (P^3 • θ) w/P

theorem cubicDualRadius_pos (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K) (w : InfinitePlace K) :
    0 < cubicDualRadius R P θ w := div_pos (cubicLinearRadius_pos R (P^3 • θ) w) hP

theorem cubicProductTailWeight_inv_le (R : ℝ) (N : ℕ) (θ u : mixedSpace K) :
    1/cubicProductTailWeight R N θ u ≤
      (2^N : ℝ)^(Fintype.card (InfinitePlace K)) *
        ∏ w : InfinitePlace K, 1/(1+normAtPlace w u/cubicLinearRadius R θ w)^N := by
  rw [cubicProductTailWeight_eq_places]
  have he : 1/(∏ w : InfinitePlace K,
      cubicTailWeight (2*R) N (normAtPlace w θ) (normAtPlace w u)) =
      ∏ w : InfinitePlace K, 1/cubicTailWeight (2*R) N (normAtPlace w θ) (normAtPlace w u) := by
    rw [Finset.prod_div_distrib,Finset.prod_const_one]
  rw [he]
  calc
    _ ≤ ∏ w : InfinitePlace K,
        2^N/(1+normAtPlace w u/cubicLinearRadius R θ w)^N := by
      apply Finset.prod_le_prod
      · intro w hw
        exact div_nonneg zero_le_one (cubicTailWeight_pos _ _ _ (normAtPlace_nonneg _ _)).le
      · intro w hw
        exact cubicTailWeight_inv_le_product (2*R) N (normAtPlace_nonneg w θ) (normAtPlace_nonneg w u)
    _ = _ := by
      simp only [div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,one_mul]

/-- The same anisotropic kernel on the actual embedded ideal-dual points. -/
theorem cubicDualRadius_kernel (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K) (ξ : K) :
    (∏ w : InfinitePlace K,
      1/(1+normAtPlace w (-(P • mixedEmbedding K ξ))/cubicLinearRadius R (P^3 • θ) w)^(finrank ℚ K+2)) =
        latticeProductDecay (cubicDualRadius R P θ) 0 ξ := by
  unfold latticeProductDecay cubicDualRadius
  simp only [sub_zero,normAtPlace_neg,normAtPlace_smul,abs_of_pos hP]
  apply Finset.prod_congr rfl
  intro w hw
  congr 3
  field_simp

/-- Uniform actual Fourier bound in the summable fractional-ideal product kernel. -/
theorem scaledSmoothCubicFourier_lattice_decay (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 0 < P), ∀ θ : mixedSpace K, ∀ ξ : K,
      ‖traceFourier (scaledSmoothPowerSchwartz 3 rho R hrho hR P hP.ne' θ) (mixedEmbedding K ξ)‖ ≤
        (C*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ)) *
          latticeProductDecay (cubicDualRadius R P θ) 0 ξ := by
  let N := finrank ℚ K+2
  obtain ⟨C,hC,hb⟩ := scaledSmoothCubicFourier_stationary_tail (K:=K) rho R hrho hR N
  let A : ℝ := (2^N)^(Fintype.card (InfinitePlace K))
  have hA : 0 < A := by unfold A; positivity
  refine ⟨C*A,mul_pos hC hA,fun P hP θ ξ => ?_⟩
  have ht := cubicProductTailWeight_inv_le R N (P^3 • θ) (-(P • mixedEmbedding K ξ))
  rw [cubicDualRadius_kernel R P hP θ ξ] at ht
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ C*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ) from
      div_nonneg (mul_nonneg hC.le (pow_nonneg hP.le _)) (cubicProductStationaryWeight_pos _).le)
  calc
    _ ≤ C*P^(finrank ℚ K)/(cubicProductStationaryWeight (P^3 • θ)*
        cubicProductTailWeight R N (P^3 • θ) (-(P • mixedEmbedding K ξ))) := hb P hP θ (mixedEmbedding K ξ)
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,mul_inv,one_mul,A,mul_assoc,mul_left_comm,mul_comm] using hm

#print axioms scaledSmoothCubicFourier_lattice_decay
end WaringSiegel.WSL3Poisson
