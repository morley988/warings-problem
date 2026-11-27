import WaringSiegel.WSL3PoissonMixedKernelFamily
import WaringSiegel.WSL3PoissonMixedBox

/-!
# The actual smooth cubic Weyl minor-arc bound

The epsilon loss is the proved divisor compression over O_K. The long-thin
Poisson kernel is evaluated on the literal inverse different. The statement
keeps the exact frequency `6θ`, scale `4P³`, and conductor cutoff `P^d`.
-/
noncomputable section
set_option maxHeartbeats 600000
open Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem doubleTranslated_linear_minor_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ Θ : mixedSpace K,
      (∀ γ : K, P^finrank ℚ K <
        (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
          productArcWeight (P^2*(4*P)) (Θ-mixedEmbedding K γ)) →
      ∀ H : Finset (𝓞 K), (∀ h ∈ H, ‖mixedEmbedding K (h:K)‖ ≤ 2*P) →
      (∑ h ∈ H, ∑ j ∈ H,
        ‖compactLinearSum (fun x => doubleTranslatedProductWeight w
          ((P⁻¹ • mixedEmbedding K (h:K),P⁻¹ • mixedEmbedding K (j:K)),x)) P
            (Θ*mixedEmbedding K ((h*j:𝓞 K):K))‖) ≤
        C * (P^finrank ℚ K)^2 * P^ε := by
  obtain ⟨Cw,hCw,hpoint⟩ := compactLinearFamily_kernel_bound
    (doubleTranslatedProductWeight_contDiff hw)
    (isCompact_closedBall (0:mixedSpace K × mixedSpace K) 2) hc
    (fun a => (doubleTranslatedProductWeight_support a).trans subset_closure)
  obtain ⟨Cd,hCd,hdiv⟩ := numberField_product_kernel_rpow_bound (K:=K) hε
  let Z := linearLongThinKernel (0:mixedSpace K) 1 0
  let A := shiftBoxConstant K
  let B := originalLongThinProductConstant K
  have hZ : 0 ≤ Z := linearLongThinKernel_nonneg _ _ _
  have hA : 0 < A := shiftBoxConstant_pos
  have hB : 0 < B := originalLongThinProductConstant_pos
  let C := Cw*(2*A*Z+Cd*B*(4:ℝ)^finrank ℚ K)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun P hP Θ hminor H hH => ?_⟩
  have hP0 : 0 < P := by linarith
  have h4P : 0 < 4*P := by positivity
  let F := linearLongThinKernel Θ P
  have hF : ∀ y, 0 ≤ F y := linearLongThinKernel_nonneg Θ P
  have hcard : (H.card:ℝ) ≤ A*P^finrank ℚ K := shiftBox_card_bound P hP H hH
  have hzero : F 0 ≤ Z := by
    dsimp [F,Z]
    rw [linearLongThinKernel_at_zero]
    exact linearLongThinKernel_zero_le P hP
  have hprod : ∀ y ∈ shiftProducts H, ‖mixedEmbedding K (y:K)‖ ≤ P*(4*P) :=
    fun y hy => shiftProducts_mixed_norm_bound P hP0.le H hH hy
  have hparam (h j : 𝓞 K) (hh : h ∈ H) (hj : j ∈ H) :
      (P⁻¹ • mixedEmbedding K (h:K),P⁻¹ • mixedEmbedding K (j:K)) ∈
        Metric.closedBall (0:mixedSpace K × mixedSpace K) 2 := by
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def]
    exact max_le (normalized_shift_norm_le_two P hP0 (hH h hh))
      (normalized_shift_norm_le_two P hP0 (hH j hj))
  have hcorr : (∑ h ∈ H, ∑ j ∈ H,
      ‖compactLinearSum (fun x => doubleTranslatedProductWeight w
        ((P⁻¹ • mixedEmbedding K (h:K),P⁻¹ • mixedEmbedding K (j:K)),x)) P
          (Θ*mixedEmbedding K ((h*j:𝓞 K):K))‖) ≤
      Cw*P^finrank ℚ K * (∑ h ∈ H, ∑ j ∈ H, F (h*j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact hpoint P (4*P) hP0 h4P Θ (h*j)
      (hprod _ (Finset.mem_image.mpr ⟨(h,j),Finset.mem_product.mpr ⟨hh,hj⟩,rfl⟩))
      _ (hparam h j hh hj)
  have hsum : (∑ y ∈ (shiftProducts H).filter (fun y => y ≠ 0), F y) ≤
      B*(4:ℝ)^finrank ℚ K * P^finrank ℚ K := by
    have h1 := linearLongThinKernel_sum_le Θ P (4*P) hP0 h4P
      ((shiftProducts H).filter (fun y => y ≠ 0))
      (fun y hy => hprod y (Finset.mem_filter.mp hy).1)
    have h2 := (originalLongThinProductDecay_minor_bound Θ P (4*P) hP (by linarith)
      (by nlinarith) hminor).2
    exact h1.trans (h2.trans_eq (by dsimp [B]; rw [mul_pow]; ring))
  have hcomp := hdiv P hP H (fun h hh v => by
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans (hH h hh)) F hF
  have hε1 : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hdiag : 2*(H.card:ℝ)*F 0 ≤ 2*A*Z*P^finrank ℚ K*P^ε := by
    calc
      _ ≤ 2*(A*P^finrank ℚ K)*Z := by gcongr; exact hF 0
      _ = 2*A*Z*P^finrank ℚ K := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hε1
  have hoff := mul_le_mul_of_nonneg_left hsum (show 0 ≤ Cd*P^ε by positivity)
  have hfinal : (∑ h ∈ H, ∑ j ∈ H, F (h*j)) ≤
      (2*A*Z+Cd*B*(4:ℝ)^finrank ℚ K)*P^finrank ℚ K*P^ε := by
    exact hcomp.trans ((add_le_add hdiag hoff).trans_eq (by ring))
  exact hcorr.trans ((mul_le_mul_of_nonneg_left hfinal (by positivity)).trans_eq (by dsimp [C]; ring))

/-- A genuine cubic Weyl bound for the original compact smooth sum. -/
theorem compactCubicSum_minor_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ θ α β : mixedSpace K,
      (∀ γ : K, P^finrank ℚ K <
        (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
          productArcWeight (P^2*(4*P)) ((6: mixedSpace K)*θ-mixedEmbedding K γ)) →
      ‖compactCubicSum w P θ α β‖^4 ≤ C * (P^finrank ℚ K)^3 * P^ε := by
  obtain ⟨C,hC,hbound⟩ := doubleTranslated_linear_minor_bound hw hc hε
  refine ⟨shiftBoxConstant K*C,mul_pos shiftBoxConstant_pos hC,fun P hP θ α β hminor => ?_⟩
  have hP0 : 0 < P := by linarith
  let S := compactIntegerSupport w hc P hP0.ne'
  let H := additiveDifferences S
  have hS : ∀ x ∈ S, ‖mixedEmbedding K (x:K)‖ ≤ P :=
    fun x hx => compactIntegerSupport_norm_bound hc hsupport P hP0 hx
  have hH : ∀ h ∈ H, ‖mixedEmbedding K (h:K)‖ ≤ 2*P :=
    fun h hh => additiveDifferences_norm_bound S P hS hh
  have hdiff : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H := by
    intro x hx y hy
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩
  have hweyl := compactCubicSum_fourth_le_linear w hc P hP0.ne' θ α β H hdiff
  have hcorr := hbound P hP (6*θ) hminor H hH
  have he (h j : 𝓞 K) : 6*θ*mixedEmbedding K (h:K)*mixedEmbedding K (j:K) =
      (6*θ)*mixedEmbedding K ((h*j:𝓞 K):K) := by simp only [map_mul]; ring
  simp_rw [he] at hweyl
  have hcard := shiftBox_card_bound P hP H hH
  calc
    _ ≤ (H.card:ℝ) * (C*(P^finrank ℚ K)^2*P^ε) :=
      hweyl.trans (mul_le_mul_of_nonneg_left hcorr (Nat.cast_nonneg _))
    _ ≤ (shiftBoxConstant K*P^finrank ℚ K) * (C*(P^finrank ℚ K)^2*P^ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end WaringSiegel.WSL3Poisson
