import WaringSiegel.WSL4ArchLongThinKernel
import WaringSiegel.WSL4ArchArcWeights
import WaringSiegel.WSL4ConductorMultiplier
import WaringSiegel.WSL3PoissonMixedTorus

/-! # The quadratic major estimate at the exact mixed center and enlarged cutoff -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem traceConductor_six_norm_comparison (γ : K) :
    ((traceConductor (6*γ)).absNorm:ℝ) ≤ ((traceConductor γ).absNorm:ℝ) ∧
      ((traceConductor γ).absNorm:ℝ) ≤ (6:ℝ)^finrank ℚ K*((traceConductor (6*γ)).absNorm:ℝ) := by
  constructor
  · have h : (traceConductor (6*γ)).absNorm ≤ (traceConductor γ).absNorm := by
      simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap,map_ofNat] using
        traceConductor_integral_mul_norm_le (6:𝓞 K) γ
    exact_mod_cast h
  · have h := conductorIdeal_div_nat_norm_le (inverseDifferent K) inverseDifferent_ne_zero
      (6*γ) 6 (by norm_num)
    have he : (6*γ)/(6:K)=γ := by field_simp
    norm_num only [Nat.cast_ofNat] at h
    rw [he] at h
    exact_mod_cast h

theorem mixed_six_center_difference (θ : mixedSpace K) (γ : K) :
    (6:mixedSpace K)*θ-mixedEmbedding K (6*γ) = (6:ℝ) • (θ-mixedEmbedding K γ) := by
  rw [six_smul_mixed,map_mul,map_ofNat]
  ring

theorem mixed_quadratic_arc_scale (P H : ℝ) (β : mixedSpace K) :
    productArcWeight (P^2*(2*H)) ((6:ℝ) • β) =
      productArcWeight (P^2*H) ((12:ℝ) • β) := by
  simp only [productArcWeight,normAtPlace_smul,show |(6:ℝ)|=6 by norm_num,
    show |(12:ℝ)|=12 by norm_num]
  apply Finset.prod_congr rfl
  intro w hw
  congr 2
  ring

theorem compactQuadraticAverage_mixed_major_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → H ≤ P → P ≤ H^2 →
      ∀ θ : mixedSpace K, ∀ γ : K,
      θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (L*P^finrank ℚ K) γ →
      ∀ α : 𝓞 K → mixedSpace K, ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2) ≤
        C*(P^finrank ℚ K)^2*H^finrank ℚ K*P^ε /
          (((traceConductor γ).absNorm:ℝ)*productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) := by
  let L' := (12:ℝ)^finrank ℚ K*L
  have hL' : 1 ≤ L' := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_major_bound_enlarged hw hc hsupport hε L' hL'
  have hLp : 0 < L := by linarith
  refine ⟨C*(L+(6:ℝ)^finrank ℚ K),by positivity,fun P H hP hH hHP hPH θ γ hmajor α U hU0 hU => ?_⟩
  let β := θ-mixedEmbedding K γ
  let A := productArcWeight (P^2*H) β
  let A6 := productArcWeight (P^2*(2*H)) ((6:ℝ) • β)
  let Q : ℝ := (traceConductor γ).absNorm
  let Q6 : ℝ := (traceConductor (6*γ)).absNorm
  let X := P^finrank ℚ K
  have hP0 : 0 < P := by linarith
  have hH0 : 0 < H := by linarith
  have hX : 0 < X := pow_pos hP0 _
  have hQ : 0 < Q := Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ)
  have hQ6 : 0 < Q6 := Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero (6*γ))
  have hA : 0 < A := productArcWeight_pos _ _
  have hA6 : 0 < A6 := productArcWeight_pos _ _
  have hQN := traceConductor_six_norm_comparison γ
  have hAA : A ≤ A6 := by
    dsimp only [A6]
    rw [mixed_quadratic_arc_scale]
    exact productArcWeight_le_smul_fixed _ _ (by positivity) (by norm_num) β
  have hAB : A6 ≤ (12:ℝ)^finrank ℚ K*A := by
    dsimp only [A6]
    rw [mixed_quadratic_arc_scale]
    exact productArcWeight_smul_fixed _ _ (by norm_num) β
  have hm : Q*A ≤ L*X := hmajor
  have hm6 : (6*θ) ∈ productMajorArc (inverseDifferent K) (P^2*(2*H)) (L'*P^finrank ℚ K) (6*γ) := by
    change Q6*productArcWeight (P^2*(2*H)) ((6:mixedSpace K)*θ-mixedEmbedding K (6*γ)) ≤ _
    rw [mixed_six_center_difference]
    apply (mul_le_mul hQN.1 hAB hA6.le hQ.le).trans
    have hh := mul_le_mul_of_nonneg_left hm (pow_nonneg (by norm_num : (0:ℝ)≤12) (finrank ℚ K))
    simpa only [L',X,mul_assoc,mul_comm,mul_left_comm] using hh
  have hden : Q*A ≤ (6:ℝ)^finrank ℚ K*(Q6*A6) := by
    exact (mul_le_mul hQN.2 hAA hA.le (by positivity)).trans_eq (by ring)
  have hratio : X/(Q6*A6) ≤ ((6:ℝ)^finrank ℚ K*X)/(Q*A) := by
    apply (div_le_div_iff₀ (mul_pos hQ6 hA6) (mul_pos hQ hA)).mpr
    have hh := mul_le_mul_of_nonneg_left hden hX.le
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have h1 : (1:ℝ) ≤ (L*X)/(Q*A) := (one_le_div (mul_pos hQ hA)).mpr hm
  have hfactor : longThinMajorFactor (inverseDifferent K) (6*θ) P (2*H) (6*γ) ≤
      (L+(6:ℝ)^finrank ℚ K)*X/(Q*A) := by
    unfold longThinMajorFactor
    rw [mixed_six_center_difference]
    exact (add_le_add h1 hratio).trans_eq (by ring)
  have hh := hb P H hP hH hHP hPH θ (6*γ) hm6 α U hU0 hU
  apply hh.trans
  have h := mul_le_mul_of_nonneg_left hfactor
    (show 0 ≤ C*P^finrank ℚ K*H^finrank ℚ K*P^ε by positivity)
  exact h.trans_eq (by dsimp only [X,Q,A,β]; ring)

#print axioms compactQuadraticAverage_mixed_major_bound
end WaringSiegel.WSL4
