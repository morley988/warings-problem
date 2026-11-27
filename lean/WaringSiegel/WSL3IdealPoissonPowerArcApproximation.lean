import WaringSiegel.WSL3IdealPoissonCenterApproximation
import WaringSiegel.WSL3IdealPoissonCubicMajor

/-!
# Uniform actual main-term error in conductor product-arc coordinates

For every degree k and every N, the error is bounded by C_N P^d A^N(1+A),
where A=Norm(traceConductor gamma)*productArcWeight(P^k,theta)/P^d.
Thus genuinely small product arcs give arbitrary rapid power savings.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 800000
variable {K : Type*} [Field K] [NumberField K]

def powerArcRatio (k : ℕ) (P : ℝ) (θ : mixedSpace K) (I : Ideal (𝓞 K)) : ℝ :=
  (I.absNorm:ℝ)*productArcWeight (P^k) θ/P^(finrank ℚ K)

def powerRadiusConstant (k : ℕ) (K : Type*) [Field K] [NumberField K] (R : ℝ) : ℝ :=
  |(NumberField.discr K:ℝ)| * (2*powerLinearTailThreshold k (2*R))^(finrank ℚ K)

theorem powerRadiusConstant_nonneg (k : ℕ) (R : ℝ) : 0 ≤ powerRadiusConstant k K R := by
  have hB := powerLinearTailThreshold_ge_one k (2*R)
  unfold powerRadiusConstant
  positivity

theorem powerArcRatio_nonneg (k : ℕ) (P : ℝ) (hP : 0 < P) (θ : mixedSpace K) (I : Ideal (𝓞 K)) :
    0 ≤ powerArcRatio k P θ I :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (productArcWeight_pos _ _).le) (pow_nonneg hP.le _)

theorem powerDualRadius_volume (k : ℕ) (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    (∏ w, (powerDualRadius k R P θ w)^(mult w)) =
      (powerLinearTailThreshold k (2*R)/P)^(finrank ℚ K)*
        ∏ w : InfinitePlace K, (1+P^k*normAtPlace w θ)^(mult w) := by
  have he (w : InfinitePlace K) : powerDualRadius k R P θ w =
      (powerLinearTailThreshold k (2*R)/P)*(1+P^k*normAtPlace w θ) := by
    simp only [powerDualRadius,powerLinearRadius,normAtPlace_smul,abs_of_pos (pow_pos hP k)]
    ring
  simp_rw [he,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]

theorem powerDualVolumeRatio_nonneg (k : ℕ) (R P : ℝ) (hP : 0 < P) (θ : mixedSpace K)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) : 0 ≤ powerDualVolumeRatio k R P θ I := by
  unfold powerDualVolumeRatio
  exact div_nonneg (Finset.prod_nonneg (fun w _ => pow_nonneg (powerDualRadius_pos k R P hP θ w).le _))
    (fractionalIdeal_absNorm_pos _ (fractionalTraceDual_ne_zero (integralIdealAsUnit I hI))).le

/-- The actual anisotropic dual volume is controlled by the actual conductor arc ratio. -/
theorem powerDualVolumeRatio_le_arcRatio (k : ℕ) (R P : ℝ) (hP : 0 < P)
    (θ : mixedSpace K) (I : Ideal (𝓞 K)) :
    powerDualVolumeRatio k R P θ I ≤ powerRadiusConstant k K R*powerArcRatio k P θ I := by
  have hB := powerLinearTailThreshold_ge_one k (2*R)
  have hfac : 0 ≤ (powerLinearTailThreshold k (2*R)/P)^(finrank ℚ K) := by positivity
  have hv := mul_le_mul_of_nonneg_left
    (one_add_place_product_le_arcWeight (P^k) (pow_nonneg hP.le k) θ) hfac
  rw [← powerDualRadius_volume k R P hP θ] at hv
  unfold powerDualVolumeRatio
  rw [integralIdeal_traceDual_absNorm,div_eq_mul_inv,mul_inv,inv_inv,inv_inv]
  have hh := mul_le_mul_of_nonneg_right hv
    (show 0 ≤ |(NumberField.discr K:ℝ)| * (I.absNorm:ℝ) by positivity)
  exact hh.trans_eq (by
    unfold powerRadiusConstant powerArcRatio
    rw [div_pow,mul_pow]
    ring)

/-- Every-degree uniform field-center main term with an explicit arbitrarily
high power of the genuine conductor/product-arc ratio. No Weil hypothesis. -/
theorem smoothPower_center_main_error_arcWeight (k : ℕ) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖(∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^k)) -
        (P^(finrank ℚ K)/(((traceConductor γ).absNorm:ℝ)*
          basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
          (fieldCenterCompleteSum k γ 0 * weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ))‖ ≤
        C*P^(finrank ℚ K)*(powerArcRatio k P θ (traceConductor γ))^N*
          (1+powerArcRatio k P θ (traceConductor γ)) := by
  obtain ⟨C,hC,hb⟩ := smoothPower_center_main_error (K:=K) k rho R hrho hR N
  let D : ℝ := 1+powerRadiusConstant k K R
  have hD : 1 ≤ D := by dsimp only [D]; linarith [powerRadiusConstant_nonneg (K:=K) k R]
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨C*D^(N+1),by positivity,fun γ P hP θ => ?_⟩
  let a := powerArcRatio k P θ (traceConductor γ)
  let b := powerDualVolumeRatio k R P θ (traceConductor γ)
  have ha : 0 ≤ a := powerArcRatio_nonneg k P hP θ _
  have hb0 : 0 ≤ b := powerDualVolumeRatio_nonneg k R P hP θ _ (traceConductor_ne_zero γ)
  have hba : b ≤ D*a := by
    have h := powerDualVolumeRatio_le_arcRatio k R P hP θ (traceConductor γ)
    dsimp only [D]
    nlinarith
  have hadd : 1+b ≤ D*(1+a) := by nlinarith
  have hprod := mul_le_mul (pow_le_pow_left₀ hb0 hba N) hadd
    (by linarith : 0 ≤ 1+b) (pow_nonneg (mul_nonneg hDp.le ha) N)
  have hh := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le (pow_nonneg hP.le (finrank ℚ K)))
  apply (hb γ P hP θ).trans
  exact (show C*P^(finrank ℚ K)*b^N*(1+b) ≤
      (C*P^(finrank ℚ K))*((D*a)^N*(D*(1+a))) from by simpa only [mul_assoc] using hh).trans_eq (by
        rw [mul_pow,pow_succ]
        dsimp only [a]
        ring)

#print axioms powerDualVolumeRatio_le_arcRatio
#print axioms smoothPower_center_main_error_arcWeight
end WaringSiegel.WSL3Poisson
