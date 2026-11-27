import WaringSiegel.WSL3PoissonUniformTrace
import WaringSiegel.WSL3PoissonCompactLinear
import WaringSiegel.WSL3PoissonMixedKernelBounds

/-!
# Uniform long-thin linear estimates for actual smooth amplitude families

Different integer frequencies may use different members of one fixed compact
smooth family. This is the precise uniformity needed for translated product
weights after quadratic or cubic differencing.
-/

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped ContDiff BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem archimedeanProductDecay_neg (m : ℕ) (x : mixedSpace K) :
    archimedeanProductDecay m (-x) = archimedeanProductDecay m x := by
  simp only [archimedeanProductDecay, normAtPlace_neg]

def longThinFinitePairEmbed (S : Finset (𝓞 K)) (P H : ℝ)
    (hbox : ∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) :
    (S × inverseDifferent K) → originalLongThinDomain (K:=K) P H :=
  fun p => ⟨(-p.2, p.1), hbox p.1 p.1.property⟩

theorem longThinFinitePairEmbed_injective (S : Finset (𝓞 K)) (P H : ℝ)
    (hbox : ∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) :
    Function.Injective (longThinFinitePairEmbed S P H hbox) := by
  intro p q h
  have he := congrArg Subtype.val h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.snd he)
  · exact neg_injective (congrArg Prod.fst he)

theorem longThinFinitePairEmbed_kernel (θ : mixedSpace K) (P H : ℝ) (S : Finset (𝓞 K))
    (hbox : ∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) (y : S) (ξ : inverseDifferent K) :
    originalLongThinProductDecay θ P (longThinFinitePairEmbed S P H hbox (y,ξ)) =
      archimedeanProductDecay (2*finrank ℚ K+2)
        (P • (mixedEmbedding K (ξ:K)-θ*mixedEmbedding K ((y:𝓞 K):K))) := by
  change archimedeanProductDecay _
    (P • (mixedEmbedding K (-(ξ:K))+θ*mixedEmbedding K ((y:𝓞 K):K))) = _
  simp only [map_neg]
  have h : -mixedEmbedding K (ξ:K)+θ*mixedEmbedding K ((y:𝓞 K):K) =
      -(mixedEmbedding K (ξ:K)-θ*mixedEmbedding K ((y:𝓞 K):K)) := by abel
  rw [h, smul_neg, archimedeanProductDecay_neg]

/-- The analytic comparison is uniform over one jointly smooth compact family. -/
theorem compactLinearFamily_longThin_kernel_bound
    {F : A × mixedSpace K → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set A} {B : Set (mixedSpace K)} (hT : IsCompact T) (hB : IsCompact B)
    (hFs : ∀ a, support (fun x => F (a,x)) ⊆ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 0 < P → 0 < H → ∀ θ : mixedSpace K,
      ∀ S : Finset (𝓞 K), (∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) →
      ∀ a : S → A, (∀ y, a y ∈ T) →
      (∑ y : S, ‖compactLinearSum (fun x => F (a y,x)) P
        (θ*mixedEmbedding K ((y:𝓞 K):K))‖) ≤
      C * P^(finrank ℚ K) *
        (∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p) := by
  obtain ⟨C, hC, hdec⟩ := uniform_traceFourier_product_decay hF hT hB hFs (2*finrank ℚ K+2)
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C/c, div_pos hC hc, fun P H hP hH θ S hbox a ha => ?_⟩
  let e := longThinFinitePairEmbed S P H hbox
  have he : Function.Injective e := longThinFinitePairEmbed_injective S P H hbox
  have hs := (originalLongThinProductDecay_summable_bound θ P H hP hH).1
  have hs' := hs.comp_injective he
  have hsub : (∑' p : S × inverseDifferent K, originalLongThinProductDecay θ P (e p)) ≤
      ∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p := by
    exact Summable.tsum_le_tsum_of_inj e he
      (fun p hp => archimedeanProductDecay_nonneg _ _) (fun _ => le_rfl) hs' hs
  have hpoint (y : S) :
      ‖compactLinearSum (fun x => F (a y,x)) P (θ*mixedEmbedding K ((y:𝓞 K):K))‖ ≤
        (C/c) * P^(finrank ℚ K) *
          (∑' ξ : inverseDifferent K, originalLongThinProductDecay θ P (e (y,ξ))) := by
    have hfa : ContDiff ℝ ∞ (fun x => F (a y,x)) := hF.comp (contDiff_const.prodMk contDiff_id)
    have hca : HasCompactSupport (fun x => F (a y,x)) :=
      HasCompactSupport.of_support_subset_isCompact hB (hFs (a y))
    have hnorm : ‖∑' ξ : inverseDifferent K, traceFourier (fun x => F (a y,x))
        (P • (mixedEmbedding K (ξ:K)-θ*mixedEmbedding K ((y:𝓞 K):K)))‖ ≤
        C * (∑' ξ : inverseDifferent K, originalLongThinProductDecay θ P (e (y,ξ))) := by
      apply tsum_of_norm_bounded ((hs'.prod_factor y).hasSum.mul_left C)
      intro ξ
      dsimp only [Function.comp_apply]
      rw [show e (y,ξ) = longThinFinitePairEmbed S P H hbox (y,ξ) from rfl,
        longThinFinitePairEmbed_kernel]
      exact hdec (a y) (ha y) _
    rw [poisson_compact_linear _ hfa hca P hP, _root_.norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (pow_pos hP _) hc)]
    exact (mul_le_mul_of_nonneg_left hnorm (div_pos (pow_pos hP _) hc).le).trans_eq (by ring)
  calc
    _ ≤ ∑ y : S, (C/c) * P^(finrank ℚ K) *
        (∑' ξ : inverseDifferent K, originalLongThinProductDecay θ P (e (y,ξ))) :=
      Finset.sum_le_sum (fun y _ => hpoint y)
    _ = ((C/c) * P^(finrank ℚ K)) *
        (∑' p : S × inverseDifferent K, originalLongThinProductDecay θ P (e p)) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Function.comp_apply, tsum_fintype] using hs'.tsum_prod.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsub (by positivity)

theorem compactLinearFamily_longThin_minor_bound
    {F : A × mixedSpace K → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set A} {B : Set (mixedSpace K)} (hT : IsCompact T) (hB : IsCompact B)
    (hFs : ∀ a, support (fun x => F (a,x)) ⊆ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → P ≤ H^2 → ∀ θ : mixedSpace K,
      (∀ γ : K, P^finrank ℚ K <
        (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
          productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) →
      ∀ S : Finset (𝓞 K), (∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) →
      ∀ a : S → A, (∀ y, a y ∈ T) →
      (∑ y : S, ‖compactLinearSum (fun x => F (a y,x)) P
        (θ*mixedEmbedding K ((y:𝓞 K):K))‖) ≤ C * P^(finrank ℚ K) * H^(finrank ℚ K) := by
  obtain ⟨C, hC, hb⟩ := compactLinearFamily_longThin_kernel_bound hF hT hB hFs
  refine ⟨C*originalLongThinProductConstant K,
    mul_pos hC originalLongThinProductConstant_pos, fun P H hP hH hPH θ hminor S hbox a ha => ?_⟩
  apply (hb P H (by linarith) (by linarith) θ S hbox a ha).trans
  have hh := mul_le_mul_of_nonneg_left
    (originalLongThinProductDecay_minor_bound θ P H hP hH hPH hminor).2
    (show 0 ≤ C*P^(finrank ℚ K) by positivity)
  exact hh.trans_eq (by ring)

theorem compactLinearFamily_longThin_major_bound
    {F : A × mixedSpace K → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set A} {B : Set (mixedSpace K)} (hT : IsCompact T) (hB : IsCompact B)
    (hFs : ∀ a, support (fun x => F (a,x)) ⊆ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → P ≤ H^2 → ∀ θ : mixedSpace K,
      ∀ γ : K, θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (P^finrank ℚ K) γ →
      ∀ S : Finset (𝓞 K), (∀ y ∈ S, ‖mixedEmbedding K (y:K)‖ ≤ P*H) →
      ∀ a : S → A, (∀ y, a y ∈ T) →
      (∑ y : S, ‖compactLinearSum (fun x => F (a y,x)) P
        (θ*mixedEmbedding K ((y:𝓞 K):K))‖) ≤ C * P^(finrank ℚ K) * H^(finrank ℚ K) *
          longThinMajorFactor (inverseDifferent K) θ P H γ := by
  obtain ⟨C, hC, hb⟩ := compactLinearFamily_longThin_kernel_bound hF hT hB hFs
  refine ⟨C*originalLongThinProductConstant K,
    mul_pos hC originalLongThinProductConstant_pos, fun P H hP hH hPH θ γ hmaj S hbox a ha => ?_⟩
  apply (hb P H (by linarith) (by linarith) θ S hbox a ha).trans
  have hh := mul_le_mul_of_nonneg_left
    (originalLongThinProductDecay_major_bound θ P H hP hH hPH γ hmaj).2
    (show 0 ≤ C*P^(finrank ℚ K) by positivity)
  exact hh.trans_eq (by ring)

end WaringSiegel.WSL3Poisson
