import WaringSiegel.WSL3PoissonMixedLinearFamily

/-! # A common positive kernel for all members of a smooth amplitude family -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Module Function NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped ContDiff BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def linearLongThinKernel (θ : mixedSpace K) (P : ℝ) (y : 𝓞 K) : ℝ :=
  ∑' ξ : inverseDifferent K, archimedeanProductDecay (2*finrank ℚ K+2)
    (P • (mixedEmbedding K (ξ:K)-θ*mixedEmbedding K (y:K)))

theorem linearLongThinKernel_nonneg (θ : mixedSpace K) (P : ℝ) (y : 𝓞 K) :
    0 ≤ linearLongThinKernel θ P y := tsum_nonneg (fun _ => archimedeanProductDecay_nonneg _ _)

theorem linearLongThinKernel_summable (θ : mixedSpace K) (P H : ℝ) (hP : 0 < P) (hH : 0 < H)
    (y : 𝓞 K) (hy : ‖mixedEmbedding K (y:K)‖ ≤ P*H) :
    Summable (fun ξ : inverseDifferent K => archimedeanProductDecay (2*finrank ℚ K+2)
      (P • (mixedEmbedding K (ξ:K)-θ*mixedEmbedding K (y:K)))) := by
  let S : Finset (𝓞 K) := {y}
  have hb : ∀ z ∈ S, ‖mixedEmbedding K (z:K)‖ ≤ P*H := by
    intro z hz
    have he : z = y := Finset.mem_singleton.mp hz
    simpa only [he] using hy
  let e := longThinFinitePairEmbed S P H hb
  have hs := (originalLongThinProductDecay_summable_bound θ P H hP hH).1.comp_injective
    (longThinFinitePairEmbed_injective S P H hb)
  have hsy := hs.prod_factor (⟨y,Finset.mem_singleton_self y⟩ : S)
  simpa only [Function.comp_apply, longThinFinitePairEmbed_kernel] using hsy

theorem linearLongThinKernel_sum_le (θ : mixedSpace K) (P H : ℝ) (hP : 0 < P) (hH : 0 < H)
    (S : Finset (𝓞 K)) (hS : ∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) :
    (∑ y ∈ S, linearLongThinKernel θ P y) ≤
      ∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p := by
  let e := longThinFinitePairEmbed S P H hS
  have hs := (originalLongThinProductDecay_summable_bound θ P H hP hH).1
  have hi := longThinFinitePairEmbed_injective S P H hS
  have hs' := hs.comp_injective hi
  have hsub : (∑' p : S × inverseDifferent K, originalLongThinProductDecay θ P (e p)) ≤
      ∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p :=
    Summable.tsum_le_tsum_of_inj e hi
      (fun p hp => archimedeanProductDecay_nonneg _ _) (fun _ => le_rfl) hs' hs
  calc
    _ = ∑ y : S, linearLongThinKernel θ P (y:𝓞 K) := by simp only [Finset.sum_coe_sort]
    _ = ∑ y : S, ∑' ξ : inverseDifferent K, originalLongThinProductDecay θ P (e (y,ξ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply tsum_congr
      intro ξ
      exact (longThinFinitePairEmbed_kernel θ P H S hS y ξ).symm
    _ = ∑' p : S × inverseDifferent K, originalLongThinProductDecay θ P (e p) := by
      simpa only [Function.comp_apply, tsum_fintype] using hs'.tsum_prod.symm
    _ ≤ _ := hsub

/-- A single common nonnegative kernel dominates every permitted amplitude. -/
theorem compactLinearFamily_kernel_bound
    {F : A × mixedSpace K → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set A} {B : Set (mixedSpace K)} (hT : IsCompact T) (hB : IsCompact B)
    (hFs : ∀ a, support (fun x => F (a,x)) ⊆ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 0 < P → 0 < H → ∀ θ : mixedSpace K,
      ∀ y : 𝓞 K, ‖mixedEmbedding K (y:K)‖ ≤ P*H → ∀ a ∈ T,
      ‖compactLinearSum (fun x => F (a,x)) P (θ*mixedEmbedding K (y:K))‖ ≤
        C * P^(finrank ℚ K) * linearLongThinKernel θ P y := by
  obtain ⟨C,hC,hdec⟩ := uniform_traceFourier_product_decay hF hT hB hFs (2*finrank ℚ K+2)
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C/c, div_pos hC hc, fun P H hP hH θ y hy a ha => ?_⟩
  have hfa : ContDiff ℝ ∞ (fun x => F (a,x)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hca : HasCompactSupport (fun x => F (a,x)) :=
    HasCompactSupport.of_support_subset_isCompact hB (hFs a)
  have hs := linearLongThinKernel_summable θ P H hP hH y hy
  have hn : ‖∑' ξ : inverseDifferent K, traceFourier (fun x => F (a,x))
      (P • (mixedEmbedding K (ξ:K)-θ*mixedEmbedding K (y:K)))‖ ≤
      C * linearLongThinKernel θ P y :=
    tsum_of_norm_bounded (hs.hasSum.mul_left C) (fun ξ => hdec a ha _)
  rw [poisson_compact_linear _ hfa hca P hP, _root_.norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (pow_pos hP _) hc)]
  exact (mul_le_mul_of_nonneg_left hn (div_pos (pow_pos hP _) hc).le).trans_eq (by ring)

theorem archimedeanProductDecay_smul_le (m : ℕ) (P : ℝ) (hP : 1 ≤ P) (x : mixedSpace K) :
    archimedeanProductDecay m (P • x) ≤ archimedeanProductDecay m x := by
  unfold archimedeanProductDecay
  apply Finset.prod_le_prod
  · intro w hw
    exact div_nonneg zero_le_one (pow_nonneg (by linarith [normAtPlace_nonneg w (P • x)]) _)
  · intro w hw
    rw [normAtPlace_smul, abs_of_pos (show 0 < P by linarith)]
    apply one_div_le_one_div_of_le (pow_pos (by linarith [normAtPlace_nonneg w x]) _)
    apply pow_le_pow_left₀ (by linarith [normAtPlace_nonneg w x])
    nlinarith [normAtPlace_nonneg w x]

theorem linearLongThinKernel_zero_le (P : ℝ) (hP : 1 ≤ P) :
    linearLongThinKernel (0:mixedSpace K) P 0 ≤ linearLongThinKernel (0:mixedSpace K) 1 0 := by
  have hsP := linearLongThinKernel_summable (0:mixedSpace K) P 1 (by linarith) zero_lt_one 0 (by simp; linarith)
  have hs1 := linearLongThinKernel_summable (0:mixedSpace K) 1 1 zero_lt_one zero_lt_one 0 (by simp)
  apply hsP.tsum_le_tsum _ hs1
  intro ξ
  simpa only [zero_mul, sub_zero, one_smul] using
    archimedeanProductDecay_smul_le (2*finrank ℚ K+2) P hP (mixedEmbedding K (ξ:K))

@[simp] theorem linearLongThinKernel_at_zero (θ : mixedSpace K) (P : ℝ) :
    linearLongThinKernel θ P 0 = linearLongThinKernel (0:mixedSpace K) P 0 := by
  simp only [linearLongThinKernel, map_zero, mul_zero, sub_zero]

end WaringSiegel.WSL3Poisson
