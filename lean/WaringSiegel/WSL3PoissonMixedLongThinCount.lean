import WaringSiegel.WSL3PoissonMixedGaussianCount

/-!
# Polynomial counts at every enlarged original long-thin scale

Exact Gaussian Poisson at P/u,H*u² is valid for every positive u, even if
P/u<1. Its dual exponent is u² times the original exponent. For u≥1 its
dual sum decreases, while its geometric covolume grows by u^(2d). Thus the
same original minor/major estimate controls every polynomial annulus.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem longThinDualGaussian_enlarged_le (θ : mixedSpace K) (P H u : ℝ)
    (hP : P ≠ 0) (hu : 1 ≤ u) (p : 𝓞 K × K) :
    longThinDualGaussian θ (P/u) (H*u^2) p ≤ longThinDualGaussian θ P H p := by
  have hup : 0 < u := by linarith
  let Q := mixedSquareNorm (mixedEmbedding K (p.1:K))/P^2 +
    (P*H)^2*mixedSquareNorm (θ*mixedEmbedding K (p.1:K)-mixedEmbedding K p.2)
  have hQ : 0 ≤ Q := by
    unfold Q mixedSquareNorm
    positivity
  have he : mixedSquareNorm (mixedEmbedding K (p.1:K))/(P/u)^2 +
      ((P/u)*(H*u^2))^2*mixedSquareNorm (θ*mixedEmbedding K (p.1:K)-mixedEmbedding K p.2) =
        u^2*Q := by
    dsimp [Q]
    field_simp
  unfold longThinDualGaussian
  rw [he]
  apply Real.exp_le_exp.mpr
  change -(u^2*Q) ≤ -Q
  exact neg_le_neg (le_mul_of_one_le_left hQ (one_le_pow₀ hu))

/-- Enlarging every original direction by u costs at most its Euclidean volume u^(2d). -/
theorem longThinOriginalGaussian_enlarged_tsum_le (θ : mixedSpace K) (P H u : ℝ)
    (hP : P ≠ 0) (hH : 0 < H) (hu : 1 ≤ u) :
    (∑' p, longThinOriginalGaussian θ (P/u) (H*u^2) p) ≤
      u^(2*finrank ℚ K) * (∑' p, longThinOriginalGaussian θ P H p) := by
  have hup : 0 < u := by linarith
  have hHs : 0 < H*u^2 := mul_pos hH (sq_pos_of_pos hup)
  have hPs : P/u ≠ 0 := div_ne_zero hP hup.ne'
  have hscaled := (longThin_gaussian_summable θ (P/u) (H*u^2) hPs hHs.ne').1
  have horiginal := (longThin_gaussian_summable θ P H hP hH.ne').1
  have hsum := hscaled.tsum_le_tsum
    (fun p : longThinDualDomain (inverseDifferent K) =>
      longThinDualGaussian_enlarged_le θ P H u hP hu p) horiginal
  rw [poisson_longThin_gaussian θ (P/u) (H*u^2) hPs hHs,
    poisson_longThin_gaussian θ P H hP hH]
  calc
    _ ≤ ((H*u^2)^(finrank ℚ K)/((4:ℝ)^nrComplexPlaces K*Real.pi^(finrank ℚ K))) *
        (∑' p : longThinDualDomain (inverseDifferent K), longThinDualGaussian θ P H p) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Every enlarged actual thin-box count is controlled by one fixed Gaussian sum. -/
theorem originalThinBox_enlarged_card_le_gaussian (θ : mixedSpace K) (P H u : ℝ)
    (hP : 0 < P) (hH : 0 < H) (hu : 1 ≤ u)
    (S : Finset (inverseDifferent K × 𝓞 K))
    (he : ∀ p ∈ S, ‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖ ≤ u/P)
    (hv : ∀ p ∈ S, ‖mixedEmbedding K (p.2:K)‖ ≤ u*(P*H)) :
    (S.card:ℝ) ≤ originalGaussianBoxFactor K * u^(2*finrank ℚ K) *
      (∑' p, longThinOriginalGaussian θ P H p) := by
  have hup : 0 < u := by linarith
  have hb := originalThinBox_card_le_gaussian θ (P/u) (H*u^2)
    (div_pos hP hup) (mul_pos hH (sq_pos_of_pos hup)) S
    (by simpa only [inv_div] using he)
    (by intro p hp; convert hv p hp using 1 <;> field_simp <;> ring)
  apply hb.trans
  have h := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_enlarged_tsum_le θ P H u hP.ne' hH hu)
    (originalGaussianBoxFactor_pos (K:=K)).le
  exact h.trans_eq (by ring)

theorem originalThinBox_enlarged_minor_card_bound (θ : mixedSpace K) (P H u : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (hu : 1 ≤ u)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ))
    (S : Finset (inverseDifferent K × 𝓞 K))
    (he : ∀ p ∈ S, ‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖ ≤ u/P)
    (hv : ∀ p ∈ S, ‖mixedEmbedding K (p.2:K)‖ ≤ u*(P*H)) :
    (S.card:ℝ) ≤ originalThinMinorConstant K * H^(finrank ℚ K) * u^(2*finrank ℚ K) := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  apply (originalThinBox_enlarged_card_le_gaussian θ P H u hPp hHp hu S he hv).trans
  have hb := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_minor_bound θ P H hP hH hPH hminor).2
    (show 0 ≤ originalGaussianBoxFactor K * u^(2*finrank ℚ K) by
      exact mul_nonneg originalGaussianBoxFactor_pos.le (by positivity))
  exact hb.trans_eq (by unfold originalThinMinorConstant; ring)

theorem originalThinBox_enlarged_major_card_bound (θ : mixedSpace K) (P H u : ℝ)
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (hu : 1 ≤ u)
    (γ : K) (hmaj : θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (P^finrank ℚ K) γ)
    (S : Finset (inverseDifferent K × 𝓞 K))
    (he : ∀ p ∈ S, ‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖ ≤ u/P)
    (hv : ∀ p ∈ S, ‖mixedEmbedding K (p.2:K)‖ ≤ u*(P*H)) :
    (S.card:ℝ) ≤
      (originalThinMinorConstant K * H^(finrank ℚ K) *
        longThinMajorFactor (inverseDifferent K) θ P H γ) * u^(2*finrank ℚ K) := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  apply (originalThinBox_enlarged_card_le_gaussian θ P H u hPp hHp hu S he hv).trans
  have hb := mul_le_mul_of_nonneg_left
    (longThinOriginalGaussian_major_bound θ P H hP hH hPH γ hmaj).2
    (show 0 ≤ originalGaussianBoxFactor K * u^(2*finrank ℚ K) by
      exact mul_nonneg originalGaussianBoxFactor_pos.le (by positivity))
  exact hb.trans_eq (by unfold originalThinMinorConstant; ring)

end WaringSiegel.WSL3Poisson
