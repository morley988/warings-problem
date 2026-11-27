import WaringSiegel.WSL3PoissonCompactLinear
import WaringSiegel.WSL3PoissonShiftedSmooth

/-!
# Shifted linear minor-arc bound for every fixed smooth compact amplitude

The cutoff may be centered at zero or translated; it need not be the positive
root cutoff. Every analytic and kernel summability hypothesis is derived.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap ContDiff
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactLinearSum_product_bound (f : mixedSpace K → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ), 0 < H → ∀ β : mixedSpace K,
      Summable (fun ξ : inverseDifferent K => linearProductDecay H β (mixedEmbedding K (ξ:K))) →
      ‖compactLinearSum f H β‖ ≤ C * H^(finrank ℚ K) *
        (∑' ξ : inverseDifferent K, linearProductDecay H β (mixedEmbedding K (ξ:K))) := by
  obtain ⟨C, hC, hb⟩ := traceFourier_product_decay (hc.toSchwartzMap hf) (finrank ℚ K+2)
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc' : 0 < c := basisCovolume_pos _
  refine ⟨C/c, div_pos hC hc', fun H hH β hs => ?_⟩
  have hn : ‖∑' ξ : inverseDifferent K, traceFourier f (H • (mixedEmbedding K (ξ:K)-β))‖ ≤
      C * (∑' ξ : inverseDifferent K, linearProductDecay H β (mixedEmbedding K (ξ:K))) := by
    apply tsum_of_norm_bounded (hs.hasSum.mul_left C)
    intro ξ
    simpa only [linearProductDecay_eq H hH.le] using hb (H • (mixedEmbedding K (ξ:K)-β))
  rw [poisson_compact_linear f hf hc H hH, _root_.norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos (pow_pos hH _) hc')]
  calc
    _ ≤ (H^(finrank ℚ K)/c) *
        (C * (∑' ξ : inverseDifferent K, linearProductDecay H β (mixedEmbedding K (ξ:K)))) :=
      mul_le_mul_of_nonneg_left hn (div_pos (pow_pos hH _) hc').le
    _ = _ := by ring

theorem compactLinearSum_shifted_minor_bound (f : mixedSpace K → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B H : ℝ), 1 ≤ B → B^2 ≤ H → ∀ θ η : mixedSpace K,
      (∀ γ : K, B^finrank ℚ K <
        (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
          productArcWeight (B*H) (θ-mixedEmbedding K γ)) →
      ∀ S : Finset (𝓞 K),
      (∀ y ∈ S, ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (y:K)) ≤ B) →
      (∑ y : S, ‖compactLinearSum f H (θ*mixedEmbedding K ((y:𝓞 K):K)+η)‖) ≤
        C * H^(finrank ℚ K) := by
  obtain ⟨C, hC, hb⟩ := compactLinearSum_product_bound f hf hc
  have hD := shiftedPairConstant_pos (inverseDifferent K) inverseDifferent_ne_zero
  refine ⟨C * (2*shiftedPairConstant (inverseDifferent K)), by positivity,
    fun B H hB hH θ η hminor S hbox => ?_⟩
  have hHp : 0 < H := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < B)) hH
  obtain ⟨hs, hsum⟩ := shiftedPairProductDecay_summable_bound
    (inverseDifferent K) inverseDifferent_ne_zero θ η B H hB hH hminor
  let e := shiftedFinitePairEmbed S B hbox
  have he : Function.Injective e := shiftedFinitePairEmbed_injective S B hbox
  have hs' := hs.comp_injective he
  have hsmall : (∑' p : S × inverseDifferent K,
      shiftedPairProductDecay θ η H (e p)) ≤ 2*shiftedPairConstant (inverseDifferent K) := by
    apply le_trans _ hsum
    exact Summable.tsum_le_tsum_of_inj e he
      (fun p hp => shiftedPairProductDecay_nonneg θ η H hHp.le p)
      (fun _ => le_rfl) hs' hs
  calc
    _ ≤ ∑ y : S, C * H^(finrank ℚ K) *
        (∑' ξ : inverseDifferent K,
          linearProductDecay H (θ*mixedEmbedding K ((y:𝓞 K):K)+η) (mixedEmbedding K (ξ:K))) := by
      apply Finset.sum_le_sum
      intro y hy
      exact hb H hHp _ (hs'.prod_factor y)
    _ = (C * H^(finrank ℚ K)) *
        (∑' p : S × inverseDifferent K, shiftedPairProductDecay θ η H (e p)) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Function.comp_apply, tsum_fintype] using hs'.tsum_prod.symm
    _ ≤ (C * H^(finrank ℚ K)) * (2*shiftedPairConstant (inverseDifferent K)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem trace_compactLinearSum_shifted_minor_bound (f : mixedSpace K → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B H : ℝ), 1 ≤ B → B^2 ≤ H → ∀ θ η : mixedSpace K,
      ∀ k : ℕ, 0 < k →
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (B*H) ((k:ℝ)^finrank ℚ K * B^finrank ℚ K) →
      ∀ S : Finset (𝓞 K),
      (∀ y ∈ S, ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (y:K)) ≤ B) →
      (∑ y : S, ‖compactLinearSum f H (((k:ℝ) • θ)*mixedEmbedding K ((y:𝓞 K):K)+η)‖) ≤
        C * H^(finrank ℚ K) := by
  obtain ⟨C, hC, hb⟩ := compactLinearSum_shifted_minor_bound f hf hc
  refine ⟨C, hC, fun B H hB hH θ η k hk hminor S hbox => ?_⟩
  apply hb B H hB hH ((k:ℝ) • θ) η _ S hbox
  exact traceMajorArcUnion_smul_nat_preimage (B*H) (B^finrank ℚ K)
    (mul_nonneg (by linarith) (le_trans (sq_nonneg B) hH)) θ k hk hminor

end WaringSiegel.WSL3Poisson
