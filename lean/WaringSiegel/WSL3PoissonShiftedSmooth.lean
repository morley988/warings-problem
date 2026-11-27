import WaringSiegel.WSL3PoissonScaledSmooth
import WaringSiegel.WSL2ShiftedProductKernel

/-!
# Smooth linear exponential sums from the actual translated product kernel

The weight and field determine one constant before all scales, frequencies
and shifts. Exact scaled Poisson plus proved Schwartz Fourier decay bounds
the actual linear sums. WSL2 then supplies the summable translated kernel,
closing this linear analytic bridge without assuming a Poisson estimate.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def linearProductDecay (H : ℝ) (β ξ : mixedSpace K) : ℝ :=
  ∏ w, 1/(1+H*normAtPlace w (β-ξ))^(finrank ℚ K+2)

theorem linearProductDecay_eq (H : ℝ) (hH : 0 ≤ H) (β ξ : mixedSpace K) :
    archimedeanProductDecay (finrank ℚ K+2) (H • (ξ-β)) = linearProductDecay H β ξ := by
  have h : ξ-β = -(β-ξ) := by abel
  simp only [archimedeanProductDecay, linearProductDecay, normAtPlace_smul,
    abs_of_nonneg hH, h, normAtPlace_neg]

/-- One weight-dependent constant bounds every scaled linear sum by its literal
product Fourier kernel. Its summability premise is discharged in the next theorem. -/
theorem smoothLinearSum_product_bound (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ), 0 < H → ∀ β : mixedSpace K,
      Summable (fun ξ : inverseDifferent K => linearProductDecay H β (mixedEmbedding K (ξ:K))) →
      ‖smoothLinearSum ρ R H β‖ ≤ C * H^(finrank ℚ K) *
        (∑' ξ : inverseDifferent K, linearProductDecay H β (mixedEmbedding K (ξ:K))) := by
  obtain ⟨C, hC, hb⟩ := traceFourier_product_decay
    (smoothWeightSchwartz (K:=K) ρ R hρ hR) (finrank ℚ K+2)
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C/c, div_pos hC hc, fun H hH β hs => ?_⟩
  have hsum := hs.hasSum.mul_left C
  have hn : ‖∑' ξ : inverseDifferent K,
      traceFourier (smoothWeightSchwartz ρ R hρ hR) (H • (mixedEmbedding K (ξ:K)-β))‖ ≤
      C * (∑' ξ : inverseDifferent K, linearProductDecay H β (mixedEmbedding K (ξ:K))) := by
    apply tsum_of_norm_bounded hsum
    intro ξ
    simpa only [linearProductDecay_eq H hH.le] using hb (H • (mixedEmbedding K (ξ:K)-β))
  rw [poisson_smooth_linear ρ R hρ hR H hH, _root_.norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos (pow_pos hH _) hc)]
  calc
    _ ≤ (H^(finrank ℚ K)/c) *
        (C * (∑' ξ : inverseDifferent K, linearProductDecay H β (mixedEmbedding K (ξ:K)))) :=
      mul_le_mul_of_nonneg_left hn (div_pos (pow_pos hH _) hc).le
    _ = _ := by ring

def shiftedFinitePairEmbed (S : Finset (𝓞 K)) (B : ℝ)
    (hbox : ∀ y ∈ S, ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (y:K)) ≤ B) :
    (S × inverseDifferent K) → shiftedPairDomain (inverseDifferent K) B :=
  fun p => ⟨(p.1, p.2), p.2.property, hbox p.1 p.1.property⟩

theorem shiftedFinitePairEmbed_injective (S : Finset (𝓞 K)) (B : ℝ)
    (hbox : ∀ y ∈ S, ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (y:K)) ≤ B) :
    Function.Injective (shiftedFinitePairEmbed S B hbox) := by
  intro p q h
  have he := congrArg Subtype.val h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact Subtype.ext (congrArg Prod.snd he)

/-- The actual smooth linear sums have a uniform translated minor-arc bound.
All scale, shift and kernel summability hypotheses are discharged here. -/
theorem smoothLinearSum_shifted_minor_bound (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B H : ℝ), 1 ≤ B → B^2 ≤ H → ∀ θ η : mixedSpace K,
      (∀ γ : K, B^finrank ℚ K <
        (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
          productArcWeight (B*H) (θ-mixedEmbedding K γ)) →
      ∀ S : Finset (𝓞 K),
      (∀ y ∈ S, ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (y:K)) ≤ B) →
      (∑ y : S, ‖smoothLinearSum ρ R H (θ*mixedEmbedding K ((y:𝓞 K):K)+η)‖) ≤
        C * H^(finrank ℚ K) := by
  obtain ⟨C, hC, hb⟩ := smoothLinearSum_product_bound (K:=K) ρ R hρ hR
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

/-- The same bound is stated on the actual trace torus after a positive integer
phase multiplier, as required by the cubic differencing step. -/
theorem trace_smoothLinearSum_shifted_minor_bound (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B H : ℝ), 1 ≤ B → B^2 ≤ H → ∀ θ η : mixedSpace K,
      ∀ k : ℕ, 0 < k →
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (B*H) ((k:ℝ)^finrank ℚ K * B^finrank ℚ K) →
      ∀ S : Finset (𝓞 K),
      (∀ y ∈ S, ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (y:K)) ≤ B) →
      (∑ y : S, ‖smoothLinearSum ρ R H (((k:ℝ) • θ)*mixedEmbedding K ((y:𝓞 K):K)+η)‖) ≤
        C * H^(finrank ℚ K) := by
  obtain ⟨C, hC, hb⟩ := smoothLinearSum_shifted_minor_bound (K:=K) ρ R hρ hR
  refine ⟨C, hC, fun B H hB hH θ η k hk hminor S hbox => ?_⟩
  apply hb B H hB hH ((k:ℝ) • θ) η _ S hbox
  exact traceMajorArcUnion_smul_nat_preimage (B*H) (B^finrank ℚ K)
    (mul_nonneg (by linarith) (le_trans (sq_nonneg B) hH)) θ k hk hminor

end WaringSiegel.WSL3Poisson
