import WaringSiegel.WSL2ShiftedDecayKernel
import WaringSiegel.WSL2MomentLatticeProductDecay

/-!
# WSL2: literal product-decay shifted kernels

The anisotropic product kernel used after linear Poisson is dominated by the
already proved radial kernel. The resulting true infinite series is uniformly
bounded in every shift, with no Poisson identity used as a hypothesis.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem rescaleMixed_const_inv (H : ℝ) (x : mixedSpace K) :
    rescaleMixed (fun _ => H⁻¹) x = H • x := by
  ext w <;> simp [rescaleMixed, div_eq_mul_inv, smul_eq_mul, mul_comm]

def shiftedPairProductDecay (θ η : mixedSpace K) (H : ℝ) (p : 𝓞 K × K) : ℝ :=
  ∏ w, 1/(1+H*normAtPlace w
    (θ*mixedEmbedding K (p.1:K)+η-mixedEmbedding K p.2))^(finrank ℚ K+2)

theorem shiftedPairProductDecay_nonneg (θ η : mixedSpace K) (H : ℝ) (hH : 0 ≤ H)
    (p : 𝓞 K × K) : 0 ≤ shiftedPairProductDecay θ η H p := by
  unfold shiftedPairProductDecay
  apply Finset.prod_nonneg
  intro w hw
  have hn := normAtPlace_nonneg w (θ*mixedEmbedding K (p.1:K)+η-mixedEmbedding K p.2)
  positivity

theorem shiftedPairProductDecay_le_radial (θ η : mixedSpace K) (H : ℝ) (hH : 0 < H)
    (p : 𝓞 K × K) : shiftedPairProductDecay θ η H p ≤ shiftedPairDecay θ η H p := by
  have h := WSL2.mixed_product_decay_le_radial (fun _ : InfinitePlace K => H⁻¹)
    (fun _ => inv_pos.mpr hH)
    (θ*mixedEmbedding K (p.1:K)+η-mixedEmbedding K p.2)
  simpa only [shiftedPairProductDecay, shiftedPairDecay, div_inv_eq_mul, mul_comm,
    rescaleMixed_const_inv, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hH] using h

theorem shiftedPairProductDecay_summable_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (hminor : ∀ γ : K, R^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (R*H) (θ-mixedEmbedding K γ)) :
    Summable (fun p : shiftedPairDomain I R => shiftedPairProductDecay θ η H p) ∧
      (∑' p : shiftedPairDomain I R, shiftedPairProductDecay θ η H p) ≤
        2*shiftedPairConstant I := by
  have hHp : 0 < H := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < R)) hH
  obtain ⟨hs, hb⟩ := shiftedPairDecay_summable_bound I hI θ η R H hR hH hminor
  have hp := Summable.of_nonneg_of_le
    (fun p : shiftedPairDomain I R => shiftedPairProductDecay_nonneg θ η H hHp.le p)
    (fun p : shiftedPairDomain I R => shiftedPairProductDecay_le_radial θ η H hHp p) hs
  exact ⟨hp, (hp.tsum_le_tsum
    (fun p : shiftedPairDomain I R => shiftedPairProductDecay_le_radial θ η H hHp p) hs).trans hb⟩

theorem trace_shiftedPairProductDecay_summable_bound
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (k : ℕ) (hk : 0 < k)
    (hminor : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (R*H) ((k:ℝ)^finrank ℚ K * R^finrank ℚ K)) :
    Summable (fun p : shiftedPairDomain (inverseDifferent K) R =>
      shiftedPairProductDecay ((k:ℝ) • θ) η H p) ∧
      (∑' p : shiftedPairDomain (inverseDifferent K) R,
        shiftedPairProductDecay ((k:ℝ) • θ) η H p) ≤ 2*shiftedPairConstant (inverseDifferent K) := by
  apply shiftedPairProductDecay_summable_bound _ inverseDifferent_ne_zero
    ((k:ℝ) • θ) η R H hR hH
  exact traceMajorArcUnion_smul_nat_preimage (R*H) (R^finrank ℚ K)
    (mul_nonneg (by linarith) (le_trans (sq_nonneg R) hH)) θ k hk hminor

end WaringSiegel
