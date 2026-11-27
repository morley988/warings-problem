import WaringSiegel.WSL3IdealPoissonCubicBound
import WaringSiegel.WSL2ProductArcs

/-!
# Actual ideal-cubic major-arc estimate from finite twisted coefficients

The geometric major-arc condition alone bounds the complete dual lattice
series. The resulting analytic estimate retains the full real/complex
stationary weight and has no archimedean or Poisson premise.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [NumberField K]

theorem integralIdeal_traceDual_absNorm (I : Ideal (𝓞 K)) :
    (FractionalIdeal.absNorm (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹):ℝ) =
      |(NumberField.discr K:ℝ)|⁻¹*(I.absNorm:ℝ)⁻¹ := by
  rw [map_mul,map_inv₀]
  push_cast
  rw [inverseDifferent_absNorm,FractionalIdeal.coeIdeal_absNorm]
  simp only [Rat.cast_inv,Rat.cast_natCast]

theorem cubicDualRadius_volume (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    (∏ w, (cubicDualRadius R P θ w)^(mult w)) =
      (cubicTailThreshold (2*R)/P)^(finrank ℚ K)*
        ∏ w : InfinitePlace K, (1+P^3*normAtPlace w θ)^(mult w) := by
  have he (w : InfinitePlace K) : cubicDualRadius R P θ w =
      (cubicTailThreshold (2*R)/P)*(1+P^3*normAtPlace w θ) := by
    simp only [cubicDualRadius,cubicLinearRadius,normAtPlace_smul,abs_of_pos (pow_pos hP 3)]
    ring
  simp_rw [he,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]

theorem one_add_place_product_le_arcWeight (H : ℝ) (hH : 0 ≤ H) (θ : mixedSpace K) :
    (∏ w : InfinitePlace K, (1+H*normAtPlace w θ)^(mult w)) ≤
      (2:ℝ)^(finrank ℚ K)*productArcWeight H θ := by
  calc
    _ ≤ ∏ w : InfinitePlace K, (2*max 1 (H*normAtPlace w θ))^(mult w) := by
      apply Finset.prod_le_prod
      · intro w hw
        exact pow_nonneg (add_nonneg zero_le_one (mul_nonneg hH (normAtPlace_nonneg w θ))) _
      · intro w hw
        apply pow_le_pow_left₀ (add_nonneg zero_le_one (mul_nonneg hH (normAtPlace_nonneg w θ)))
        have h1 := le_max_left (1:ℝ) (H*normAtPlace w θ)
        have h2 := le_max_right (1:ℝ) (H*normAtPlace w θ)
        linarith
    _ = _ := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]
      rfl

def cubicMajorRadiusConstant (K : Type*) [Field K] [NumberField K] (R : ℝ) : ℝ :=
  |(NumberField.discr K:ℝ)| *(2*cubicTailThreshold (2*R))^(finrank ℚ K)

theorem cubicMajorRadiusConstant_nonneg (R : ℝ) : 0 ≤ cubicMajorRadiusConstant K R := by
  have hB := cubicTailThreshold_ge_one (2*R)
  unfold cubicMajorRadiusConstant
  positivity

/-- The major-arc condition controls the complete anisotropic dual volume. -/
theorem cubicDualRadius_norm_ratio_le (I : Ideal (𝓞 K)) (R P : ℝ) (hP : 0 < P)
    (θ : mixedSpace K)
    (hmaj : (I.absNorm:ℝ)*productArcWeight (P^3) θ ≤ P^(finrank ℚ K)) :
    (∏ w, (cubicDualRadius R P θ w)^(mult w))/
      (FractionalIdeal.absNorm (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹):ℝ) ≤
        cubicMajorRadiusConstant K R := by
  have hB := cubicTailThreshold_ge_one (2*R)
  have hfac : 0 ≤ (cubicTailThreshold (2*R)/P)^(finrank ℚ K) := by positivity
  have hv := mul_le_mul_of_nonneg_left
    (one_add_place_product_le_arcWeight (P^3) (pow_nonneg hP.le 3) θ) hfac
  rw [← cubicDualRadius_volume R P hP θ] at hv
  rw [integralIdeal_traceDual_absNorm,div_eq_mul_inv,mul_inv,inv_inv,inv_inv]
  calc
    _ ≤ ((cubicTailThreshold (2*R)/P)^(finrank ℚ K)*
        ((2:ℝ)^(finrank ℚ K)*productArcWeight (P^3) θ)) *
          (|(NumberField.discr K:ℝ)| *(I.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    _ = cubicMajorRadiusConstant K R *
        ((I.absNorm:ℝ)*productArcWeight (P^3) θ/P^(finrank ℚ K)) := by
      unfold cubicMajorRadiusConstant
      rw [div_pow,mul_pow]
      ring
    _ ≤ cubicMajorRadiusConstant K R*1 := mul_le_mul_of_nonneg_left
      ((div_le_one (pow_pos hP _)).mpr hmaj) (cubicMajorRadiusConstant_nonneg R)
    _ = _ := mul_one _

/-- Uniform actual major-arc bound, conditional only on the literal finite
coefficient bound. In particular B = Norm(I)*kappa gives the expected kappa factor. -/
theorem smoothCubic_residue_major_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ 0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (B : ℝ), 0 ≤ B →
      (∀ ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))‖ ≤ B) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      (I.absNorm:ℝ)*productArcWeight (P^3) θ ≤ P^(finrank ℚ K) →
      ‖∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))‖ ≤
        C*(B/(I.absNorm:ℝ))*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ) := by
  obtain ⟨C,hC,hb⟩ := smoothCubic_residue_sum_bound (K:=K) rho R hrho hR
  let A := cubicMajorRadiusConstant K R
  have hA : 0 ≤ A := cubicMajorRadiusConstant_nonneg R
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C*(1+A)/c,by positivity,fun I hI inst F B hB hcomplete P hP θ hmaj => ?_⟩
  apply (hb I hI F B hB hcomplete P hP θ).trans
  have hI0 : 0 ≤ (I.absNorm:ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (add_le_add_left
    (cubicDualRadius_norm_ratio_le I R P hP θ hmaj) 1)
    (show 0 ≤ C*B*P^(finrank ℚ K)/((I.absNorm:ℝ)*c*cubicProductStationaryWeight (P^3 • θ)) from
      div_nonneg (mul_nonneg (mul_nonneg hC.le hB) (pow_nonneg hP.le _))
        (mul_nonneg (mul_nonneg hI0 hc.le) (cubicProductStationaryWeight_pos _).le))
  exact hh.trans_eq (by dsimp only [A,c]; simp only [div_eq_mul_inv,mul_inv]; ring)

#print axioms cubicDualRadius_norm_ratio_le
#print axioms smoothCubic_residue_major_bound
end WaringSiegel.WSL3Poisson
