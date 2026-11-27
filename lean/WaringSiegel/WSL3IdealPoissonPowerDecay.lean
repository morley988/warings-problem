import WaringSiegel.WSL3IdealPoissonPowerTail
import WaringSiegel.WSL3IdealPoissonLatticeTail

/-!
# Every-degree Fourier decay in the actual anisotropic ideal kernel

The fixed source and literal trace phase satisfy every inverse power of
local linear frequencies, in a form suitable for nonzero-dual summation.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 1000000
variable (k : ℕ)
variable {K : Type*} [Field K] [NumberField K]

theorem powerLinearTailWeight_inv_le_product (R : ℝ) (N : ℕ) {t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    1/powerLinearTailWeight k R N t u ≤
      2^N/(1+u/(powerLinearTailThreshold k R*(1+t)))^N := by
  have hB := powerLinearTailThreshold_ge_one k R
  have hA : 1 ≤ powerLinearTailThreshold k R*(1+t) := by nlinarith
  have hAp : 0 < powerLinearTailThreshold k R*(1+t) := lt_of_lt_of_le zero_lt_one hA
  have hp : 0 < (1+u/(powerLinearTailThreshold k R*(1+t)))^N := by positivity
  apply (div_le_div_iff₀ (powerLinearTailWeight_pos k R N t hu) hp).mpr
  rw [one_mul]
  by_cases hreg : powerLinearTailThreshold k R*(1+t) ≤ u
  · rw [powerLinearTailWeight,if_pos hreg]
    have hdiv : u/(powerLinearTailThreshold k R*(1+t)) ≤ u := div_le_self hu hA
    calc
      _ ≤ (1+u)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2^N*(1+u)^N := le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  · rw [powerLinearTailWeight,if_neg hreg,mul_one]
    have hdiv : u/(powerLinearTailThreshold k R*(1+t)) ≤ 1 :=
      (div_le_one hAp).mpr (le_of_lt (lt_of_not_ge hreg))
    exact pow_le_pow_left₀ (by positivity) (by linarith) N

theorem powerLinearProductTailWeight_eq_places (R : ℝ) (N : ℕ) (θ u : mixedSpace K) :
    powerLinearProductTailWeight k R N θ u =
      ∏ w : InfinitePlace K, powerLinearTailWeight k (2*R) N (normAtPlace w θ) (normAtPlace w u) := by
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  unfold powerLinearProductTailWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isReal w.property,normAtPlace_apply_of_isReal w.property,
      Real.norm_eq_abs,Real.norm_eq_abs]
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isComplex w.property,normAtPlace_apply_of_isComplex w.property]

/-- Local radius in the unscaled linear variable. -/
def powerLinearRadius (R : ℝ) (θ : mixedSpace K) (w : InfinitePlace K) : ℝ :=
  powerLinearTailThreshold k (2*R)*(1+normAtPlace w θ)

theorem powerLinearRadius_pos (R : ℝ) (θ : mixedSpace K) (w : InfinitePlace K) :
    0 < powerLinearRadius k R θ w := by
  have hB := powerLinearTailThreshold_ge_one k (2*R)
  have hn := normAtPlace_nonneg w θ
  unfold powerLinearRadius
  positivity

/-- Local radius in the actual ideal-dual variable ξ. -/
def powerDualRadius (R P : ℝ) (θ : mixedSpace K) (w : InfinitePlace K) : ℝ :=
  powerLinearRadius k R (P^k • θ) w/P

theorem powerDualRadius_pos (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K) (w : InfinitePlace K) :
    0 < powerDualRadius k R P θ w := div_pos (powerLinearRadius_pos k R (P^k • θ) w) hP

theorem powerLinearProductTailWeight_inv_le (R : ℝ) (N : ℕ) (θ u : mixedSpace K) :
    1/powerLinearProductTailWeight k R N θ u ≤
      (2^N : ℝ)^(Fintype.card (InfinitePlace K)) *
        ∏ w : InfinitePlace K, 1/(1+normAtPlace w u/powerLinearRadius k R θ w)^N := by
  rw [powerLinearProductTailWeight_eq_places k]
  have he : 1/(∏ w : InfinitePlace K,
      powerLinearTailWeight k (2*R) N (normAtPlace w θ) (normAtPlace w u)) =
      ∏ w : InfinitePlace K, 1/powerLinearTailWeight k (2*R) N (normAtPlace w θ) (normAtPlace w u) := by
    rw [Finset.prod_div_distrib,Finset.prod_const_one]
  rw [he]
  calc
    _ ≤ ∏ w : InfinitePlace K,
        2^N/(1+normAtPlace w u/powerLinearRadius k R θ w)^N := by
      apply Finset.prod_le_prod
      · intro w hw
        exact div_nonneg zero_le_one (powerLinearTailWeight_pos k _ _ _ (normAtPlace_nonneg _ _)).le
      · intro w hw
        exact powerLinearTailWeight_inv_le_product k (2*R) N (normAtPlace_nonneg w θ) (normAtPlace_nonneg w u)
    _ = _ := by
      simp only [div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,one_mul]


/-- The product kernel at an actual field dual point, at arbitrary order m. -/
theorem powerDualRadius_kernel (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K) (m : ℕ) (ξ : K) :
    (∏ w : InfinitePlace K,
      1/(1+normAtPlace w (-(P • mixedEmbedding K ξ))/powerLinearRadius k R (P^k • θ) w)^m) =
        latticePowerDecay m (powerDualRadius k R P θ) ξ := by
  unfold latticePowerDecay powerDualRadius
  simp only [normAtPlace_neg,normAtPlace_smul,abs_of_pos hP]
  apply Finset.prod_congr rfl
  intro w hw
  congr 3
  field_simp

/-- Actual all-degree Fourier factors, with every product decay order. -/
theorem scaledSmoothPowerFourier_lattice_decay (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 0 < P), ∀ θ : mixedSpace K, ∀ ξ : K,
      ‖traceFourier (scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ) (mixedEmbedding K ξ)‖ ≤
        (C*P^(finrank ℚ K))*latticePowerDecay m (powerDualRadius k R P θ) ξ := by
  obtain ⟨C,hC,hb⟩ := scaledSmoothPowerFourier_product_tail (K:=K) k rho R hrho hR m
  let A : ℝ := (2^m)^(Fintype.card (InfinitePlace K))
  have hA : 0 < A := by unfold A; positivity
  refine ⟨C*A,mul_pos hC hA,fun P hP θ ξ => ?_⟩
  have ht := powerLinearProductTailWeight_inv_le k R m (P^k • θ) (-(P • mixedEmbedding K ξ))
  rw [powerDualRadius_kernel k R P hP θ m ξ] at ht
  have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg hC.le (pow_nonneg hP.le (finrank ℚ K)))
  calc
    _ ≤ C*P^(finrank ℚ K)/powerLinearProductTailWeight k R m (P^k • θ) (-(P • mixedEmbedding K ξ)) :=
      hb P hP θ (mixedEmbedding K ξ)
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,one_mul,A,mul_assoc,mul_left_comm,mul_comm] using hm

#print axioms scaledSmoothPowerFourier_lattice_decay
end WaringSiegel.WSL3Poisson
