import WaringSiegel.WSL2LongThinDualCount

/-!
# WSL2: the actual slope in a small dual box is its major-arc center

A nonzero pair on the common affine line gives the exact conductor product
bound. Norm separation then identifies its slope with any prescribed major
center, at the same determinant threshold. All statements concern literal
field centers and actual inverse-different (or fractional-ideal) membership.
-/

noncomputable section
set_option maxHeartbeats 1200000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem closePair_slope_conductor_product_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ : mixedSpace K)
    (P H u : ℝ) (hP : 0 < P) (hH : 0 < H) (hu : 0 ≤ u)
    (p : 𝓞 K × K) (hp : p ∈ closePairs I θ 0 (u*P) (fun _ => u/(P*H)))
    (hy : p.1 ≠ 0) (γ : K) (hline : p.2 = γ*(p.1:K)) :
    (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
      productArcWeight (P^2*H) (θ-mixedEmbedding K γ) ≤ u^finrank ℚ K*P^finrank ℚ K := by
  have hyI : p.1 ∈ conductorIdeal I γ := by
    change (p.1:K)*γ ∈ I
    rw [mul_comm, ← hline]
    exact hp.1
  have hy0 : (p.1:K) ≠ 0 := by exact_mod_cast hy
  have hyJ := FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ (P := K) hyI
  have hQ : (Ideal.absNorm (conductorIdeal I γ) : ℝ) ≤
      NumberField.mixedEmbedding.norm (mixedEmbedding K (p.1:K)) := by
    simpa only [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] using
      fractionalIdeal_absNorm_le_mixed_norm
        (conductorIdeal I γ : FractionalIdeal (𝓞 K)⁰ K) hyJ hy0
  have hlocal : ∀ w : InfinitePlace K,
      normAtPlace w (mixedEmbedding K (p.1:K)) *
        max 1 ((P^2*H)*normAtPlace w (θ-mixedEmbedding K γ)) ≤ u*P := by
    intro w
    have heq : (θ-mixedEmbedding K γ)*mixedEmbedding K (p.1:K) =
        θ*mixedEmbedding K (p.1:K)-mixedEmbedding K p.2 := by
      rw [hline, map_mul]
      ring
    have he := hp.2.2 w
    simp only [add_zero] at he
    have hmul : normAtPlace w (θ-mixedEmbedding K γ)*
        normAtPlace w (mixedEmbedding K (p.1:K)) ≤ u/(P*H) := by
      rw [← map_mul, heq]
      exact he
    rw [mul_max_of_nonneg _ _ (normAtPlace_nonneg _ _), mul_one]
    apply max_le (hp.2.1 w)
    calc
      _ = (P^2*H)*(normAtPlace w (θ-mixedEmbedding K γ)*
          normAtPlace w (mixedEmbedding K (p.1:K))) := by ring
      _ ≤ (P^2*H)*(u/(P*H)) := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = u*P := by field_simp
  calc
    _ ≤ NumberField.mixedEmbedding.norm (mixedEmbedding K (p.1:K)) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ) :=
      mul_le_mul_of_nonneg_right hQ (productArcWeight_pos _ _).le
    _ = ∏ w : InfinitePlace K,
        (normAtPlace w (mixedEmbedding K (p.1:K)) *
          max 1 ((P^2*H)*normAtPlace w (θ-mixedEmbedding K γ)))^mult w := by
      simp only [NumberField.mixedEmbedding.norm_apply, productArcWeight,
        mul_pow, Finset.prod_mul_distrib]
    _ ≤ ∏ w : InfinitePlace K, (u*P)^mult w := by
      apply Finset.prod_le_prod
      · intro w hw
        exact pow_nonneg (mul_nonneg (normAtPlace_nonneg _ _)
          (le_trans zero_le_one (le_max_left _ _))) _
      · intro w hw
        exact pow_le_pow_left₀ (mul_nonneg (normAtPlace_nonneg _ _)
          (le_trans zero_le_one (le_max_left _ _))) (hlocal w) _
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, mul_pow]

/-- In a sufficiently small dual box, a nonzero slope agrees with the given
major center, including all lifts in the actual archimedean space. -/
theorem closePair_slope_eq_major_center
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (θ : mixedSpace K)
    (P H u : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hu : 1 ≤ u)
    (hsmall : (8*(u*P))^finrank ℚ K *
      (∏ w : InfinitePlace K, (u/(P*H))^mult w) < (FractionalIdeal.absNorm I : ℝ))
    (γ₀ : K) (hmaj : θ ∈ productMajorArc I (P^2*H) (P^finrank ℚ K) γ₀)
    (p : 𝓞 K × K) (hp : p ∈ closePairs I θ 0 (u*P) (fun _ => u/(P*H)))
    (hy : p.1 ≠ 0) (γ : K) (hline : p.2 = γ*(p.1:K)) : γ = γ₀ := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  have hup : 0 < u := by linarith
  have hpγ := closePair_slope_conductor_product_bound I θ P H u hPp hHp hup.le p hp hy γ hline
  have hpγ₀ : θ ∈ productMajorArc I (P^2*H) (u^finrank ℚ K*P^finrank ℚ K) γ₀ := by
    exact hmaj.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hu))
  have hsep : (2:ℝ)^finrank ℚ K*(u^finrank ℚ K*P^finrank ℚ K)^2 <
      (FractionalIdeal.absNorm I : ℝ)*(P^2*H)^finrank ℚ K := by
    let d := finrank ℚ K
    have hprod : (∏ w : InfinitePlace K, (u/(P*H))^mult w) = (u/(P*H))^d := by
      rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
    have hs : (8:ℝ)^d*(u^d)^2/H^d < (FractionalIdeal.absNorm I : ℝ) := by
      convert hsmall using 1
      rw [hprod]
      simp only [mul_pow, div_pow]
      field_simp <;> ring
    have hs' := (div_lt_iff₀ (pow_pos hHp d)).mp hs
    have h28 : (2:ℝ)^d ≤ (8:ℝ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have ht : (2:ℝ)^d*(u^d)^2 < (FractionalIdeal.absNorm I : ℝ)*H^d :=
      (mul_le_mul_of_nonneg_right h28 (sq_nonneg _)).trans_lt hs'
    have h := mul_lt_mul_of_pos_right ht (pow_pos hPp d |> sq_pos_of_pos)
    simpa only [d, mul_pow, ← pow_mul, mul_assoc, mul_comm, mul_left_comm] using h
  by_contra hn
  exact Set.disjoint_left.mp
    (productMajorArcs_disjoint I hI (P^2*H) (u^finrank ℚ K*P^finrank ℚ K)
      (by positivity) (by positivity) hsep γ γ₀ hn) hpγ hpγ₀

end WaringSiegel
