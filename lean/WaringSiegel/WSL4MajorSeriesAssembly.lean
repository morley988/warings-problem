import WaringSiegel.WSL4MajorSeriesTail
import WaringSiegel.WSL4MajorSingularUniform
import WaringSiegel.WSL4MajorPoissonReplacement

/-! # Actual finite major main term versus singular series times singular integral

The sole arithmetic input is a stated weighted absolute conductor moment.
Both the product-frequency truncation error and the conductor-tail error
are proved here with one target-uniform constant.
-/
noncomputable section
set_option maxHeartbeats 1400000
open NumberField NumberField.mixedEmbedding Module WaringSiegel.WSL2 WaringSiegel.WSL3
  WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def productMajorSeries (k n : ℕ) (ρ R L : ℝ) (target : 𝓞 K) (b : mixedSpace K) : ℂ :=
  ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,rationalCenterPowerContribution k n q target *
    productSingularIntegral k n ρ R (L/((rationalTraceCenterConductor q).absNorm:ℝ)) b

local instance seriesCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

theorem smoothMajorMainIntegral_eq_productMajorSeries
    (k n : ℕ) (hk : 0<k) (ρ R L : ℝ) (target : 𝓞 K) (htarget : target≠0) :
    smoothMajorMainIntegral k n ρ R (rootScale k target) L target =
      (majorScale (K := K) k n (rootScale k target):ℂ)*
        productMajorSeries k n ρ R L target (normalizedTarget k 1 target) := by
  rw [smoothMajorMainIntegral_rootScale_formula k n hk ρ R L target htarget]
  congr 1
  simp only [productMajorSeries,rationalCentersUpTo,Finset.sum_map,
    boundedCenterAsRational_conductor]
  apply Finset.sum_congr rfl
  intro q hq
  rw [majorCompleteCoefficient_eq_rational,fieldRationalCenter_representative]
  simp only [Function.Embedding.coeFn_mk,boundedCenterAsRational_conductor]

theorem productMajorSeries_finite_truncation_error
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (δ : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ (target : 𝓞 K) (M : ℝ),
      Summable (fun q : RationalTraceCenter K =>
        ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖rationalCenterPowerContribution k (s+1) q target‖) →
      (∑' q : RationalTraceCenter K,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k (s+1) q target‖)≤M →
      ∀ L : ℝ, 1≤L → ∀ b : mixedSpace K,
        ‖productMajorSeries k (s+1) ρ R L target b-
          (∑ q ∈ rationalCentersUpTo ⌊L⌋₊,rationalCenterPowerContribution k (s+1) q target)*
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) b‖≤C*M/L^δ := by
  obtain ⟨C,hC,herror⟩ := productSingularIntegral_truncation_rpow (K := K) k s hk ρ R hρ hR δ
  refine ⟨C,hC,?_⟩
  intro target M hs hb L hL b
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLpow : 0<L^δ := Real.rpow_pos_of_pos hL0 δ
  rw [productMajorSeries,Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,
        ‖rationalCenterPowerContribution k (s+1) q target *
          productSingularIntegral k (s+1) ρ R (L/((rationalTraceCenterConductor q).absNorm:ℝ)) b-
          rationalCenterPowerContribution k (s+1) q target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) b‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,(C/L^δ)*
        (((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖rationalCenterPowerContribution k (s+1) q target‖) := by
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
          ‖rationalCenterPowerContribution k (s+1) q target‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/L^δ)*M := mul_le_mul_of_nonneg_left
      (rationalPower_finite_mass_le k (s+1) target δ M hs hb _) (div_nonneg hC.le hLpow.le)
    _ = C*M/L^δ := by ring

theorem productMajorSeries_full_truncation_error
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (δ : ℝ) (hδ : 0≤δ) :
    ∃ C : ℝ, 0<C ∧ ∀ (target : 𝓞 K) (M : ℝ),
      Summable (fun q : RationalTraceCenter K =>
        ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖rationalCenterPowerContribution k (s+1) q target‖) →
      (∑' q : RationalTraceCenter K,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k (s+1) q target‖)≤M →
      ∀ L : ℝ, 1≤L → ∀ b : mixedSpace K,
        ‖productMajorSeries k (s+1) ρ R L target b-
          powerSingularSeries k (s+1) target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) b‖≤C*M/L^δ := by
  obtain ⟨C,hC,hfinite⟩ := productMajorSeries_finite_truncation_error (K := K) k s hk ρ R hρ hR δ
  obtain ⟨D,hD,hfull⟩ := pairedSmooth_singularIntegral_uniform_norm (K := K) k s hk ρ R hρ hR
  refine ⟨C+D,by positivity,?_⟩
  intro target M hs hb L hL b
  have hM : 0≤M := (tsum_nonneg (fun q => by positivity)).trans hb
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have htail := rationalPower_conductor_truncation k (s+1) target δ M hδ hs hb L hL0
  let A := productMajorSeries k (s+1) ρ R L target b
  let B := ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,rationalCenterPowerContribution k (s+1) q target
  let T := powerSingularSeries k (s+1) target
  let J := pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1) (smoothRootWeight ρ R) b
  change ‖A-T*J‖≤_
  have he : A-T*J=(A-B*J)+(B-T)*J := by ring
  rw [he]
  calc
    _ ≤ ‖A-B*J‖+‖(B-T)*J‖ := norm_add_le _ _
    _ ≤ C*M/L^δ+(M/L^δ)*D := by
      apply add_le_add (hfinite target M hs hb L hL b)
      rw [norm_mul,norm_sub_rev]
      exact mul_le_mul htail (hfull b) (norm_nonneg _)
        (div_nonneg hM (Real.rpow_pos_of_pos hL0 δ).le)
    _ = (C+D)*M/L^δ := by ring

#print axioms smoothMajorMainIntegral_eq_productMajorSeries
#print axioms productMajorSeries_full_truncation_error
end WaringSiegel.WSL4
