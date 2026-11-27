import WaringSiegel.WSL3IdealPoissonPowerArcApproximation

/-!
# Actual multi-root major integrand approximation

The exact one-root source and main term are uniformly bounded at scale P^d
on small conductor product arcs. Their positive integer powers therefore
inherit every order of the proved one-root main-term error.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 800000
variable {K : Type*} [Field K] [NumberField K]

theorem fieldCenterCompleteSum_norm_le (k : ℕ) (γ : K) (ξ : mixedSpace K) :
    ‖fieldCenterCompleteSum k γ ξ‖ ≤ ((traceConductor γ).absNorm:ℝ) := by
  letI := fieldCenterResidueFintype γ
  have hcard : Fintype.card (𝓞 K ⧸ traceConductor γ) = (traceConductor γ).absNorm := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  apply (idealCompleteTraceFactor_norm_le (traceConductor γ)
    (fun q => fieldCenterResidueChar γ (q^k)) ξ).trans_eq
  simp only [(fieldCenterResidueChar γ).norm_apply,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,hcard]

theorem weightedRootIntegral_uniform_norm (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : mixedSpace K,
      ‖weightedRootIntegral k (smoothRootWeight rho R) θ‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothPowerLinearIntegral_product_tail (K:=K) k rho R hrho hR 0
  refine ⟨C,hC,fun θ => ?_⟩
  have he : smoothPowerLinearIntegral k rho R θ 0 =
      weightedRootIntegral k (smoothRootWeight rho R) θ := by
    simp only [smoothPowerLinearIntegral,weightedRootIntegral,archimedeanTraceCharacter,
      zero_mul,map_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  simpa only [powerLinearProductTailWeight,powerLinearTailWeight,pow_zero,ite_self,
    Finset.prod_const_one,mul_one,one_mul,div_one,he] using hb θ 0

def smoothPowerCenterSource (k : ℕ) (rho R P : ℝ) (γ : K) (θ : mixedSpace K) : ℂ :=
  ∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
    archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^k)

def smoothPowerCenterMainTerm (k : ℕ) (rho R P : ℝ) (γ : K) (θ : mixedSpace K) : ℂ :=
  (P^(finrank ℚ K)/(((traceConductor γ).absNorm:ℝ)*
    basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
      (fieldCenterCompleteSum k γ 0 * weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ))

theorem smoothPowerCenterMainTerm_norm (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖smoothPowerCenterMainTerm k rho R P γ θ‖ ≤ C*P^(finrank ℚ K) := by
  obtain ⟨C,hC,hb⟩ := weightedRootIntegral_uniform_norm (K:=K) k rho R hrho hR
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C/c,div_pos hC hc,fun γ P hP θ => ?_⟩
  letI := fieldCenterResidueFintype γ
  have hN : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff (traceConductor γ)).mpr inferInstance))
  rw [smoothPowerCenterMainTerm,_root_.norm_smul,Real.norm_of_nonneg (by positivity),norm_mul]
  calc
    _ ≤ (P^(finrank ℚ K)/(((traceConductor γ).absNorm:ℝ)*c))*
        (((traceConductor γ).absNorm:ℝ)*C) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul (fieldCenterCompleteSum_norm_le k γ 0) (hb (P^k • θ))
          (norm_nonneg _) hN.le
      · exact (div_pos (pow_pos hP _) (mul_pos hN hc)).le
    _ = _ := by field_simp

theorem complex_norm_pow_sub_pow {x y : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x^(n+1)-y^(n+1)‖ ≤ ((n:ℝ)+1)*M^n*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x^(n+1+1)-y^(n+1+1) = x^(n+1)*(x-y)+(x^(n+1)-y^(n+1))*y := by ring
    rw [show n.succ+1=n+1+1 by omega,he]
    calc
      _ ≤ ‖x^(n+1)*(x-y)‖+‖(x^(n+1)-y^(n+1))*y‖ := norm_add_le _ _
      _ = ‖x‖^(n+1)*‖x-y‖+‖x^(n+1)-y^(n+1)‖*‖y‖ := by rw [norm_mul,norm_mul,norm_pow]
      _ ≤ M^(n+1)*‖x-y‖+(((n:ℝ)+1)*M^n*‖x-y‖)*M := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx _) (norm_nonneg _)
        · exact mul_le_mul ih hy (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; push_cast; ring

/-- An actual product of s+1 identical root sources has the expected main
term with arbitrary conductor/product-arc error power, on A<=1. -/
theorem smoothPower_center_power_main_error (k s : ℕ) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      powerArcRatio k P θ (traceConductor γ) ≤ 1 →
      ‖(smoothPowerCenterSource k rho R P γ θ)^(s+1)-
        (smoothPowerCenterMainTerm k rho R P γ θ)^(s+1)‖ ≤
          C*P^(finrank ℚ K*(s+1))*(powerArcRatio k P θ (traceConductor γ))^N*
            (1+powerArcRatio k P θ (traceConductor γ)) := by
  obtain ⟨Ce,hCe,he⟩ := smoothPower_center_main_error_arcWeight (K:=K) k rho R hrho hR N
  obtain ⟨Cm,hCm,hm⟩ := smoothPowerCenterMainTerm_norm (K:=K) k rho R hrho hR
  let M := Cm+2*Ce
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨((s:ℝ)+1)*M^s*Ce,by positivity,fun γ P hP θ ha1 => ?_⟩
  let a := powerArcRatio k P θ (traceConductor γ)
  let x := smoothPowerCenterSource k rho R P γ θ
  let y := smoothPowerCenterMainTerm k rho R P γ θ
  have ha : 0 ≤ a := powerArcRatio_nonneg k P hP θ _
  have herr : ‖x-y‖ ≤ Ce*P^(finrank ℚ K)*a^N*(1+a) := he γ P hP θ
  have hprod : a^N*(1+a) ≤ 2 := by
    calc
      _ ≤ 1*2 := mul_le_mul (pow_le_one₀ ha ha1) (by linarith) (by linarith) zero_le_one
      _ = _ := one_mul _
  have herr2 : ‖x-y‖ ≤ (2*Ce)*P^(finrank ℚ K) := by
    apply herr.trans
    have h := mul_le_mul_of_nonneg_left hprod (mul_nonneg hCe.le (pow_nonneg hP.le (finrank ℚ K)))
    exact (show Ce*P^(finrank ℚ K)*a^N*(1+a) ≤ (Ce*P^(finrank ℚ K))*2 by
      simpa only [mul_assoc] using h).trans_eq (by ring)
  have hy0 : ‖y‖ ≤ Cm*P^(finrank ℚ K) := hm γ P hP θ
  have hx : ‖x‖ ≤ M*P^(finrank ℚ K) := by
    apply (norm_le_norm_sub_add x y).trans
    exact (add_le_add herr2 hy0).trans_eq (by dsimp only [M]; ring)
  have hy : ‖y‖ ≤ M*P^(finrank ℚ K) :=
    hy0.trans (mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith) (pow_nonneg hP.le _))
  have hp := complex_norm_pow_sub_pow (mul_nonneg hM.le (pow_nonneg hP.le _)) hx hy s
  apply hp.trans
  have hh := mul_le_mul_of_nonneg_left herr
    (show 0 ≤ ((s:ℝ)+1)*(M*P^(finrank ℚ K))^s by positivity)
  exact hh.trans_eq (by
    dsimp only [a]
    simp only [Nat.mul_add,Nat.mul_one,pow_add,pow_mul,mul_pow]
    ring)

#print axioms smoothPowerCenterMainTerm_norm
#print axioms smoothPower_center_power_main_error
end WaringSiegel.WSL3Poisson
