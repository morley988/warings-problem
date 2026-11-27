import WaringSiegel.WSL2ShiftedPairKernel
import WaringSiegel.WSL2ConductorScaling
import WaringSiegel.WSL2MomentLatticeDecay

/-!
# WSL2: a genuine summable shifted lattice kernel on minor arcs

The index set is the actual bounded integer y-box times the entire inverse
 different (or any fractional ideal). The shift is arbitrary. Integer annuli
and the proved uniform close-pair estimate give a convergent decay sum with
an explicit constant independent of the scale and of the shift.

This closes the geometric decay-kernel estimate. The passage from a smooth
linear exponential sum to this lattice kernel still requires Poisson summation.
-/

noncomputable section
set_option maxHeartbeats 1000000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def shiftedPairDomain (I : FractionalIdeal (𝓞 K)⁰ K) (R : ℝ) : Set (𝓞 K × K) :=
  {p | p.2 ∈ I ∧ ∀ w, normAtPlace w (mixedEmbedding K (p.1:K)) ≤ R}

def shiftedPairDecay (θ η : mixedSpace K) (H : ℝ) (p : 𝓞 K × K) : ℝ :=
  1/(1+H*‖θ*mixedEmbedding K (p.1:K)+η-mixedEmbedding K p.2‖)^(finrank ℚ K+2)

theorem shiftedPairDecay_nonneg (θ η : mixedSpace K) (H : ℝ) (hH : 0 ≤ H)
    (p : 𝓞 K × K) : 0 ≤ shiftedPairDecay θ η H p := by
  unfold shiftedPairDecay
  positivity

theorem shiftedPairDecay_finite_sum_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (hminor : ∀ γ : K, R^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (R*H) (θ-mixedEmbedding K γ))
    (S : Finset (shiftedPairDomain I R)) :
    (∑ p ∈ S, shiftedPairDecay θ η H p) ≤ 2*shiftedPairConstant I := by
  have hHp : 0 < H := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < R)) hH
  let rad : shiftedPairDomain I R → ℝ := fun p =>
    H*‖θ*mixedEmbedding K ((p:𝓞 K × K).1:K)+η-mixedEmbedding K (p:𝓞 K × K).2‖
  apply WSL2.finite_annular_decay_bound S rad
    (fun p _ => mul_nonneg hHp.le (norm_nonneg _)) (finrank ℚ K)
    (shiftedPairConstant I) (shiftedPairConstant_pos I hI).le
  intro n
  let T := S.filter (fun p => ⌊rad p⌋₊=n)
  have hZ : ∀ _w : InfinitePlace K, 0 < ((n:ℝ)+1)/H := fun _ => div_pos (by positivity) hHp
  have hmaps : ∀ p ∈ (T : Set (shiftedPairDomain I R)),
      (p:𝓞 K × K) ∈ closePairs I θ η R (fun _ => ((n:ℝ)+1)/H) := by
    intro p hp
    refine ⟨p.property.1, p.property.2, ?_⟩
    intro w
    have hf := (Finset.mem_filter.mp hp).2
    have ht : rad p < (n:ℝ)+1 := by
      simpa only [hf] using Nat.lt_floor_add_one (rad p)
    apply (le_div_iff₀ hHp).mpr
    have hn := normAtPlace_le_mixed_norm
      (θ*mixedEmbedding K ((p:𝓞 K × K).1:K)+η-mixedEmbedding K (p:𝓞 K × K).2) w
    exact (mul_le_mul_of_nonneg_right hn hHp.le).trans (by
      change _ ≤ (n:ℝ)+1
      dsimp [rad] at ht
      nlinarith)
  have hcard : T.card ≤ (closePairs I θ η R (fun _ => ((n:ℝ)+1)/H)).ncard := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard_of_injOn (s := (T : Set (shiftedPairDomain I R)))
        (fun p => (p:𝓞 K × K)) hmaps (fun _ _ _ _ h => Subtype.ext h)
        (closePairs_finite I hI θ η R hR _ hZ)
  have hbound := closePairs_minor_uniform_bound I hI θ η R H hR hH
    (fun _ => (n:ℝ)+1) (fun _ => by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) hminor
  have hle : (T.card:ℝ) ≤ _ := (Nat.cast_le.mpr hcard).trans hbound
  simpa only [T, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq] using hle

/-- Absolute convergence and a scale-free bound for the literal kernel. -/
theorem shiftedPairDecay_summable_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (hminor : ∀ γ : K, R^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (R*H) (θ-mixedEmbedding K γ)) :
    Summable (fun p : shiftedPairDomain I R => shiftedPairDecay θ η H p) ∧
      (∑' p : shiftedPairDomain I R, shiftedPairDecay θ η H p) ≤ 2*shiftedPairConstant I := by
  have hHp : 0 ≤ H := le_trans (sq_nonneg R) hH
  have hb := shiftedPairDecay_finite_sum_bound I hI θ η R H hR hH hminor
  have hs := summable_of_sum_le (fun p : shiftedPairDomain I R => shiftedPairDecay_nonneg θ η H hHp p) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

/-- The actual trace-torus minor arcs imply the genuine shifted decay-kernel
bound, uniformly in η and including any fixed positive integer multiplier. -/
theorem trace_shiftedPairDecay_summable_bound
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (k : ℕ) (hk : 0 < k)
    (hminor : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (R*H) ((k:ℝ)^finrank ℚ K * R^finrank ℚ K)) :
    Summable (fun p : shiftedPairDomain (inverseDifferent K) R =>
      shiftedPairDecay ((k:ℝ) • θ) η H p) ∧
      (∑' p : shiftedPairDomain (inverseDifferent K) R,
        shiftedPairDecay ((k:ℝ) • θ) η H p) ≤ 2*shiftedPairConstant (inverseDifferent K) := by
  have hHp : 0 ≤ H := le_trans (sq_nonneg R) hH
  apply shiftedPairDecay_summable_bound _ inverseDifferent_ne_zero ((k:ℝ) • θ) η R H hR hH
  exact traceMajorArcUnion_smul_nat_preimage (R*H) (R^finrank ℚ K)
    (mul_nonneg (by linarith) hHp) θ k hk hminor

end WaringSiegel
