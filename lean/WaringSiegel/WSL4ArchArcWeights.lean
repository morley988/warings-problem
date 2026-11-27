import WaringSiegel.WSL4ArchPacking

/-! # Exact comparisons with the manuscript product arc weight -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem cubicProductFrequencyWeight_places (e : ℝ) (θ : mixedSpace K) :
    cubicProductFrequencyWeight e θ =
      ∏ w : InfinitePlace K, (1+normAtPlace w θ)^((mult w:ℝ)*e) := by
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  unfold cubicProductFrequencyWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isReal w.property,Real.norm_eq_abs,mult_isReal]
    norm_num
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isComplex w.property,mult_isComplex]
    norm_num

theorem productArcWeight_rpow_le_frequencyWeight (H : ℝ) (hH : 0 ≤ H)
    (e : ℝ) (he : 0 ≤ e) (θ : mixedSpace K) :
    (productArcWeight H θ)^e ≤ cubicProductFrequencyWeight e (H • θ) := by
  rw [cubicProductFrequencyWeight_places,productArcWeight,
    ← Real.finset_prod_rpow _ _ (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) e]
  apply Finset.prod_le_prod (fun w _ => Real.rpow_nonneg (pow_nonneg
    (le_trans zero_le_one (le_max_left _ _)) _) _)
  intro w hw
  rw [← Real.rpow_natCast,← Real.rpow_mul (le_trans zero_le_one (le_max_left _ _)),
    normAtPlace_smul,abs_of_nonneg hH]
  exact Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _))
    (max_le (by nlinarith [normAtPlace_nonneg w θ]) (by linarith))
    (mul_nonneg (Nat.cast_nonneg _) he)

theorem productArcWeight_smul_fixed (H c : ℝ) (hc : 1 ≤ c) (θ : mixedSpace K) :
    productArcWeight H (c • θ) ≤ c^finrank ℚ K * productArcWeight H θ := by
  have hc0 : 0 ≤ c := by linarith
  calc
    _ ≤ ∏ w : InfinitePlace K, (c*max 1 (H*normAtPlace w θ))^mult w := by
      apply Finset.prod_le_prod (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      intro w hw
      apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
      rw [normAtPlace_smul,abs_of_nonneg hc0]
      apply max_le
      · exact le_trans hc (le_mul_of_one_le_right hc0 (le_max_left _ _))
      · nlinarith [mul_le_mul_of_nonneg_left (le_max_right 1 (H*normAtPlace w θ)) hc0]
    _ = _ := by
      simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
        InfinitePlace.sum_mult_eq,productArcWeight]

theorem productArcWeight_le_smul_fixed (H c : ℝ) (hH : 0 ≤ H) (hc : 1 ≤ c)
    (θ : mixedSpace K) : productArcWeight H θ ≤ productArcWeight H (c • θ) := by
  unfold productArcWeight
  apply Finset.prod_le_prod (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  intro w hw
  apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
  apply max_le_max le_rfl
  rw [normAtPlace_smul,abs_of_nonneg (by linarith : 0 ≤ c)]
  nlinarith [mul_nonneg hH (normAtPlace_nonneg w θ)]

/-- The exact two terms in the enlarged-major U estimate, before a fixed
integer multiplier is transferred through the arithmetic conductor. -/
theorem nearZeroCubic_center_two_term_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (κ : ℝ), 0 ≤ κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖∑' x : 𝓞 K, nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)‖ ≤
          C*κ*(P^(finrank ℚ K)*(productArcWeight (P^3) θ)^(-(1/3):ℝ)+
            ((traceConductor γ).absNorm:ℝ)*(productArcWeight (P^3) θ)^((2/3):ℝ)) := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubic_center_packing_bound (K:=K)
  refine ⟨C,hC,fun γ κ hκ hfinite P hP θ => ?_⟩
  let A := productArcWeight (P^3) θ
  have hA : 0 < A := productArcWeight_pos _ _
  have hQ : 0 ≤ ((traceConductor γ).absNorm:ℝ) := Nat.cast_nonneg _
  have hW : 0 < P^finrank ℚ K := pow_pos hP _
  have hS := cubicProductFrequencyWeight_pos (1/3) (P^3 • θ)
  have hpow : A^((1:ℝ)/3) ≤ cubicProductFrequencyWeight (1/3) (P^3 • θ) :=
    productArcWeight_rpow_le_frequencyWeight _ (pow_nonneg hP.le _) _ (by norm_num) _
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hC.le hκ) hW.le)
      (Real.rpow_pos_of_pos hA _) hpow)
    (show 0 ≤ 1+((traceConductor γ).absNorm:ℝ)*A/P^finrank ℚ K by positivity)
  apply (hb γ κ hκ hfinite P hP θ).trans (hh.trans_eq ?_)
  have hneg : A^(-(1/3):ℝ) = (A^((1:ℝ)/3))⁻¹ := Real.rpow_neg hA.le _
  have htwo : A^((2:ℝ)/3) = A*A^(-(1/3):ℝ) := by
    calc
      _ = A^((1:ℝ)+(-(1/3))) := by congr 1; norm_num
      _ = A^((1:ℝ))*A^(-(1/3):ℝ) := Real.rpow_add hA _ _
      _ = _ := by rw [Real.rpow_one]
  change C*κ*P^finrank ℚ K / A^((1:ℝ)/3) *
    (1+((traceConductor γ).absNorm:ℝ)*A/P^finrank ℚ K) =
      C*κ*(P^finrank ℚ K*A^(-(1/3):ℝ)+((traceConductor γ).absNorm:ℝ)*A^((2:ℝ)/3))
  rw [htwo,hneg]
  field_simp [hW.ne',(Real.rpow_pos_of_pos hA ((1:ℝ)/3)).ne']
  <;> ring

#print axioms nearZeroCubic_center_two_term_bound
end WaringSiegel.WSL4
