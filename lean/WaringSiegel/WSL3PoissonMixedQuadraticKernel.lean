import WaringSiegel.WSL3PoissonMixedKernelFamily
import WaringSiegel.WSL3PoissonMixedBox
import WaringSiegel.WSL3PoissonMixedCompression

/-! # Actual quadratic average reduced to the original long-thin kernel -/
noncomputable section
set_option maxHeartbeats 600000
open Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem rectangleProducts_mixed_norm_bound (P H : ℝ) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (U V : Finset (𝓞 K))
    (hU : ∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H)
    (hV : ∀ j ∈ V, ‖mixedEmbedding K (j:K)‖ ≤ 2*P)
    {y : 𝓞 K} (hy : y ∈ rectangleProducts U V) :
    ‖mixedEmbedding K (y:K)‖ ≤ P*(2*H) := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
  have he : mixedEmbedding K ((p.1*p.2:𝓞 K):K) =
      mixedEmbedding K (p.1:K)*mixedEmbedding K (p.2:K) := by simp only [map_mul]
  rw [he]
  have hb := mul_le_mul (hU p.1 (Finset.mem_product.mp hp).1)
    (hV p.2 (Finset.mem_product.mp hp).2) (norm_nonneg _) hH
  exact (norm_mul_le _ _).trans (hb.trans_eq (by ring))

/-- Exact amplitude uniformity and divisor compression, with the only remaining
quantity being the actual, already summable original long-thin kernel. -/
theorem translated_rectangle_kernel_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 0 < H → H ≤ P →
      ∀ Θ : mixedSpace K, ∀ U V : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) →
      (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∀ j ∈ V, ‖mixedEmbedding K (j:K)‖ ≤ 2*P) →
      (∑ h ∈ U, ∑ j ∈ V,
        ‖compactLinearSum (fun x => translatedProductWeight w (P⁻¹ • mixedEmbedding K (j:K),x)) P
          (Θ*mixedEmbedding K ((h*j:𝓞 K):K))‖) ≤
        C*P^finrank ℚ K * ((U.card:ℝ) + P^ε *
          (∑' p : originalLongThinDomain (K:=K) P (2*H), originalLongThinProductDecay Θ P p)) := by
  obtain ⟨Cw,hCw,hpoint⟩ := compactLinearFamily_kernel_bound
    (translatedProductWeight_contDiff hw) (isCompact_closedBall (0:mixedSpace K) 2) hc
    (fun a => (translatedProductWeight_support a).trans subset_closure)
  obtain ⟨Cd,hCd,hdiv⟩ := numberField_rectangle_kernel_rpow_bound (K:=K) hε
  let Z := linearLongThinKernel (0:mixedSpace K) 1 0
  have hZ : 0 ≤ Z := linearLongThinKernel_nonneg _ _ _
  let C := Cw*(Z+Cd+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun P H hP hH hHP Θ U V hU0 hU hV => ?_⟩
  have hP0 : 0 < P := by linarith
  let F := linearLongThinKernel Θ P
  let L := ∑' p : originalLongThinDomain (K:=K) P (2*H), originalLongThinProductDecay Θ P p
  have hL : 0 ≤ L := tsum_nonneg (fun _ => archimedeanProductDecay_nonneg _ _)
  have hF : ∀ y, 0 ≤ F y := linearLongThinKernel_nonneg Θ P
  have hzero : F 0 ≤ Z := by
    dsimp [F,Z]
    rw [linearLongThinKernel_at_zero]
    exact linearLongThinKernel_zero_le P hP
  have hprod : ∀ y ∈ rectangleProducts U V, ‖mixedEmbedding K (y:K)‖ ≤ P*(2*H) :=
    fun y hy => rectangleProducts_mixed_norm_bound P H hP0.le hH.le U V hU hV hy
  have hcorr : (∑ h ∈ U, ∑ j ∈ V,
      ‖compactLinearSum (fun x => translatedProductWeight w (P⁻¹ • mixedEmbedding K (j:K),x)) P
        (Θ*mixedEmbedding K ((h*j:𝓞 K):K))‖) ≤
      Cw*P^finrank ℚ K * (∑ h ∈ U, ∑ j ∈ V, F (h*j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    apply hpoint P (2*H) hP0 (by positivity) Θ (h*j)
      (hprod _ (Finset.mem_image.mpr ⟨(h,j),Finset.mem_product.mpr ⟨hh,hj⟩,rfl⟩))
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      normalized_shift_norm_le_two P hP0 (hV j hj)
  have hsum : (∑ y ∈ (rectangleProducts U V).filter (fun y => y ≠ 0), F y) ≤ L :=
    linearLongThinKernel_sum_le Θ P (2*H) hP0 (by positivity)
      ((rectangleProducts U V).filter (fun y => y ≠ 0))
      (fun y hy => hprod y (Finset.mem_filter.mp hy).1)
  have hcomp := hdiv P hP U V hU0 (fun h hh v => by
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans ((hU h hh).trans (by linarith)))
    (fun j hj v => by rw [← normAtPlace_apply]; exact (normAtPlace_le_mixed_norm _ v).trans (hV j hj)) F hF
  have hd := mul_le_mul_of_nonneg_left hzero (Nat.cast_nonneg U.card)
  have ho := mul_le_mul_of_nonneg_left hsum (show 0 ≤ Cd*P^ε by positivity)
  have ht : (∑ h ∈ U, ∑ j ∈ V, F (h*j)) ≤ (Z+Cd+1)*((U.card:ℝ)+P^ε*L) := by
    apply hcomp.trans
    apply (add_le_add hd ho).trans
    have hnU : 0 ≤ (U.card:ℝ) := Nat.cast_nonneg _
    have hnL : 0 ≤ P^ε*L := by positivity
    nlinarith [mul_nonneg hZ hnL, mul_nonneg hCd.le hnU]
  exact hcorr.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by dsimp [C]; ring))

/-- The original quadratic average with arbitrary lower coefficient functions. -/
theorem compactQuadraticAverage_kernel_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 0 < H → H ≤ P →
      ∀ θ : mixedSpace K, ∀ α : 𝓞 K → mixedSpace K, ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2) ≤
        C*P^finrank ℚ K * ((U.card:ℝ) + P^ε *
          (∑' p : originalLongThinDomain (K:=K) P (2*H), originalLongThinProductDecay (6*θ) P p)) := by
  obtain ⟨C,hC,hb⟩ := translated_rectangle_kernel_bound hw hc hε
  refine ⟨C,hC,fun P H hP hH hHP θ α U hU0 hU => ?_⟩
  have hP0 : 0 < P := by linarith
  let S := compactIntegerSupport w hc P hP0.ne'
  let V := additiveDifferences S
  have hS : ∀ x ∈ S, ‖mixedEmbedding K (x:K)‖ ≤ P :=
    fun x hx => compactIntegerSupport_norm_bound hc hsupport P hP0 hx
  have hV : ∀ j ∈ V, ‖mixedEmbedding K (j:K)‖ ≤ 2*P :=
    fun j hj => additiveDifferences_norm_bound S P hS hj
  have hdiff : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ V := by
    intro x hx y hy
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩
  have hpoint (h : 𝓞 K) :
      ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2 ≤
        ∑ j ∈ V, ‖compactLinearSum (fun x => translatedProductWeight w
          (P⁻¹ • mixedEmbedding K (j:K),x)) P ((6*θ)*mixedEmbedding K ((h*j:𝓞 K):K))‖ := by
    have he (j : 𝓞 K) : 2*(3*θ*mixedEmbedding K (h:K))*mixedEmbedding K (j:K) =
        (6*θ)*mixedEmbedding K ((h*j:𝓞 K):K) := by simp only [map_mul]; ring
    simpa only [he] using compactQuadraticSum_sq_le_linear w hc P hP0.ne'
      (3*θ*mixedEmbedding K (h:K)) (α h) V hdiff
  exact (Finset.sum_le_sum (fun h hh => hpoint h)).trans (hb P H hP hH hHP (6*θ) U V hU0 hU hV)

end WaringSiegel.WSL3Poisson
