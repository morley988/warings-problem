import WaringSiegel.WSL3IdealPoissonCubicDecay

/-!
# Summed actual ideal-cubic Poisson bound

Every archimedean estimate, actual dual-ideal identification, and anisotropic
lattice-series convergence premise is discharged. The only optional arithmetic
input is a uniform bound for the literal finite twisted complete coefficients.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 500000
variable {K : Type*} [Field K] [NumberField K]

theorem fractionalIdeal_product_decay_zero (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w) :
    Summable (fun ξ : I => latticeProductDecay R 0 (ξ:K)) ∧
      (∑' ξ : I, latticeProductDecay R 0 (ξ:K)) ≤
        2*(3:ℝ)^(finrank ℚ K)*(1+(∏ w, (R w)^(mult w))/(FractionalIdeal.absNorm I:ℝ)) := by
  have h := fractionalIdeal_product_decay_summable I hI 0 0 R hR
  have he : (fun z : K => z-0 ∈ I) = (fun z : K => z ∈ I) := by
    funext z
    rw [sub_zero]
  rw [he] at h
  exact h

/-- The exact ideal-coset source admits a fully summed anisotropic stationary
bound. A finite-sum estimate is the sole arithmetic hypothesis. -/
theorem smoothCubic_residue_sum_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ 0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (B : ℝ), 0 ≤ B →
      (∀ ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))‖ ≤ B) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))‖ ≤
        (C*B*P^(finrank ℚ K)/((I.absNorm:ℝ)*
          basisCovolume (NumberField.mixedEmbedding.latticeBasis K)*cubicProductStationaryWeight (P^3 • θ))) *
          (1+(∏ w, (cubicDualRadius R P θ w)^(mult w))/
            (FractionalIdeal.absNorm (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹):ℝ)) := by
  obtain ⟨C,hC,hdec⟩ := scaledSmoothCubicFourier_lattice_decay (K:=K) rho R hrho hR
  refine ⟨C*(2*(3:ℝ)^(finrank ℚ K)),by positivity,fun I hI inst F B hB hcomplete P hP θ => ?_⟩
  let D : FractionalIdeal (𝓞 K)⁰ K := inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹
  have hD : D ≠ 0 := fractionalTraceDual_ne_zero (integralIdealAsUnit I hI)
  let A : ℝ := C*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hC.le (pow_nonneg hP.le _))
    (cubicProductStationaryWeight_pos _).le
  let r := cubicDualRadius R P θ
  have hr (w : InfinitePlace K) : 0 < r w := cubicDualRadius_pos R P hP θ w
  obtain ⟨hs,hcount⟩ := fractionalIdeal_product_decay_zero D hD r hr
  let f := scaledSmoothPowerSchwartz 3 rho R hrho hR P hP.ne' θ
  have hnorm : ‖∑' ξ : D,
      idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))*traceFourier f (mixedEmbedding K (ξ:K))‖ ≤
        (B*A)*(∑' ξ : D, latticeProductDecay r 0 (ξ:K)) := by
    apply tsum_of_norm_bounded (hs.hasSum.mul_left (B*A))
    intro ξ
    rw [norm_mul]
    calc
      _ ≤ B*(A*latticeProductDecay r 0 (ξ:K)) :=
        mul_le_mul (hcomplete ξ) (hdec P hP θ (ξ:K)) (norm_nonneg _) hB
      _ = _ := by ring
  have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_left hcount (mul_nonneg hB hA))
  have hIN : 0 < (I.absNorm:ℝ) := by
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr inferInstance))
  have hc := basisCovolume_pos (NumberField.mixedEmbedding.latticeBasis K)
  have he : (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
      (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))) =
      ∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*f (mixedEmbedding K (x:K)) := by
    apply tsum_congr
    intro x
    rw [show f (mixedEmbedding K (x:K)) =
      smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3) from
          scaledSmoothPowerSchwartz_apply 3 rho R hrho hR P hP.ne' θ _]
  rw [he,poisson_ideal_residue_weight I hI F f,_root_.norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hIN.le hc.le))]
  have hh := mul_le_mul_of_nonneg_left hnorm'
    (show 0 ≤ ((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ by positivity)
  exact hh.trans_eq (by
    dsimp only [A,r,D]
    simp only [div_eq_mul_inv,mul_inv]
    ring)

#print axioms fractionalIdeal_product_decay_zero
#print axioms smoothCubic_residue_sum_bound
end WaringSiegel.WSL3Poisson
