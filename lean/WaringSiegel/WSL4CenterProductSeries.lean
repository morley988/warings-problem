import WaringSiegel.WSL4CenterSeriesTail
import WaringSiegel.WSL4MajorSeriesAssembly

/-! # Actual product-arc truncation for arbitrary rational-center coefficients -/
noncomputable section
set_option maxHeartbeats 1400000
open NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def productCenterSeries (k n : ℕ) (ρ R L : ℝ) (f : RationalTraceCenter K → ℂ)
    (b : mixedSpace K) : ℂ :=
  ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,f q *
    productSingularIntegral k n ρ R (L/((rationalTraceCenterConductor q).absNorm:ℝ)) b

theorem productCenterSeries_finite_truncation_error
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (δ : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ (f : RationalTraceCenter K → ℂ) (M : ℝ),
      Summable (fun q : RationalTraceCenter K =>
        ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖f q‖) →
      (∑' q : RationalTraceCenter K,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖)≤M →
      ∀ L : ℝ, 1≤L → ∀ b : mixedSpace K,
        ‖productCenterSeries k (s+1) ρ R L f b-
          (∑ q ∈ rationalCentersUpTo ⌊L⌋₊,f q)*
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) b‖≤C*M/L^δ := by
  obtain ⟨C,hC,herror⟩ := productSingularIntegral_truncation_rpow (K := K) k s hk ρ R hρ hR δ
  refine ⟨C,hC,?_⟩
  intro f M hs hb L hL b
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLpow : 0<L^δ := Real.rpow_pos_of_pos hL0 δ
  rw [productCenterSeries,Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,
        ‖f q *
          productSingularIntegral k (s+1) ρ R (L/((rationalTraceCenterConductor q).absNorm:ℝ)) b-
          f q *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) b‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,(C/L^δ)*
        (((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖f q‖) := by
      apply Finset.sum_le_sum
      intro q hq
      have hN0 : 0<((rationalTraceCenterConductor q).absNorm:ℝ) :=
        lt_of_lt_of_le zero_lt_one (rationalTraceCenter_norm_one_le q)
      have hN : ((rationalTraceCenterConductor q).absNorm:ℝ)≤L :=
        (Nat.cast_le.mpr ((mem_rationalCentersUpTo _ q).mp hq)).trans (Nat.floor_le hL0.le)
      have hQ : 1≤L/((rationalTraceCenterConductor q).absNorm:ℝ) := (one_le_div hN0).mpr hN
      rw [← mul_sub,norm_mul,norm_sub_rev]
      apply (mul_le_mul_of_nonneg_left (herror _ hQ b) (norm_nonneg _)).trans_eq
      rw [Real.div_rpow hL0.le hN0.le]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    _ = (C/L^δ)*∑ q ∈ rationalCentersUpTo ⌊L⌋₊,
        ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖f q‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/L^δ)*M := mul_le_mul_of_nonneg_left
      (rationalCenterSeries_finite_mass_le f δ M hs hb _) (div_nonneg hC.le hLpow.le)
    _ = C*M/L^δ := by ring

theorem productCenterSeries_full_truncation_error
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (δ : ℝ) (hδ : 0≤δ) :
    ∃ C : ℝ, 0<C ∧ ∀ (f : RationalTraceCenter K → ℂ) (M : ℝ),
      Summable (fun q : RationalTraceCenter K =>
        ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖f q‖) →
      (∑' q : RationalTraceCenter K,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖)≤M →
      ∀ L : ℝ, 1≤L → ∀ b : mixedSpace K,
        ‖productCenterSeries k (s+1) ρ R L f b-
          (∑' q,f q) *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) b‖≤C*M/L^δ := by
  obtain ⟨C,hC,hfinite⟩ := productCenterSeries_finite_truncation_error (K := K) k s hk ρ R hρ hR δ
  obtain ⟨D,hD,hfull⟩ := pairedSmooth_singularIntegral_uniform_norm (K := K) k s hk ρ R hρ hR
  refine ⟨C+D,by positivity,?_⟩
  intro f M hs hb L hL b
  have hM : 0≤M := (tsum_nonneg (fun q => by positivity)).trans hb
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have htail := rationalCenterSeries_conductor_truncation f δ M hδ hs hb L hL0
  let A := productCenterSeries k (s+1) ρ R L f b
  let B := ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,f q
  let T := (∑' q,f q)
  let J := pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1) (smoothRootWeight ρ R) b
  change ‖A-T*J‖≤_
  have he : A-T*J=(A-B*J)+(B-T)*J := by ring
  rw [he]
  calc
    _ ≤ ‖A-B*J‖+‖(B-T)*J‖ := norm_add_le _ _
    _ ≤ C*M/L^δ+(M/L^δ)*D := by
      apply add_le_add (hfinite f M hs hb L hL b)
      rw [norm_mul,norm_sub_rev]
      exact mul_le_mul htail (hfull b) (norm_nonneg _)
        (div_nonneg hM (Real.rpow_pos_of_pos hL0 δ).le)
    _ = (C+D)*M/L^δ := by ring

#print axioms productCenterSeries_finite_truncation_error
#print axioms productCenterSeries_full_truncation_error
end WaringSiegel.WSL4Local
