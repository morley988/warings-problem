import WaringSiegel.WSL3UnitPowerLinearPruning

/-!
# Every-degree rapid tails for the actual ideal Poisson Fourier factors

This is the literal Fourier transform appearing in exact ideal-coset
Poisson. The constant is independent of scale and both mixed frequencies.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem scaledSmoothPowerFourier_product_tail (k : ℕ) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 0 < P), ∀ θ ξ : mixedSpace K,
      ‖traceFourier (scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ) ξ‖ ≤
        (C*P^(finrank ℚ K))/powerLinearProductTailWeight k R N (P^k • θ) (-(P • ξ)) := by
  obtain ⟨C,hC,hb⟩ := smoothPowerLinearIntegral_product_tail (K:=K) k rho R hrho hR N
  refine ⟨C,hC,fun P hP θ ξ => ?_⟩
  rw [traceFourier_scaledSmoothPower k rho R hrho hR P hP,_root_.norm_smul,
    Real.norm_of_nonneg (pow_nonneg hP.le _)]
  have h := mul_le_mul_of_nonneg_left (hb (P^k • θ) (-(P • ξ)))
    (pow_nonneg hP.le (finrank ℚ K))
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h

#print axioms scaledSmoothPowerFourier_product_tail
end WaringSiegel.WSL3Poisson
