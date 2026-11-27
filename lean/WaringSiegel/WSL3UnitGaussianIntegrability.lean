import WaringSiegel.WSL3UnitGaussianLimit

/-!
# Positive frequency integrals from Gaussian regularization

Monotone convergence upgrades a finite limit of Gaussian-regularized
nonnegative integrals to genuine absolute integrability. No frequency L¹
premise is included in this conclusion.
-/
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 800000

theorem integrable_of_gaussian_integrals_tendsto {q : V → ℝ}
    (hq : AEStronglyMeasurable q) (hpos : ∀ x, 0 ≤ q x)
    (hint : ∀ n : ℕ, Integrable (fun x : V =>
      Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x))
    {L : ℝ} (hlim : Tendsto (fun n : ℕ => ∫ x : V,
      Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x) atTop (𝓝 L)) :
    Integrable q := by
  let a : ℕ → V → ℝ := fun n x =>
    Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x
  have ha_pos (n : ℕ) (x : V) : 0 ≤ a n x := mul_nonneg (Real.exp_pos _).le (hpos x)
  have hinv : Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have ha_lim (x : V) : Tendsto (fun n => a n x) atTop (𝓝 (q x)) := by
    have ht : Tendsto (fun n : ℕ => - (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) atTop (𝓝 0) := by
      simpa using hinv.neg.mul_const (‖x‖^2)
    have he := ((Real.continuous_exp.tendsto 0).comp ht).mul_const (q x)
    simpa only [Real.exp_zero, one_mul] using he
  have ha_mono (x : V) : Monotone (fun n => ENNReal.ofReal (a n x)) := by
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (hpos x)
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_mul]
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hmono := lintegral_tendsto_of_tendsto_of_monotone
    (μ := (volume : Measure V))
    (fun n => (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall ha_mono)
    (Eventually.of_forall (fun x => ENNReal.tendsto_ofReal (ha_lim x)))
  have ht : Tendsto (fun n => ∫⁻ x : V, ENNReal.ofReal (a n x)) atTop
      (𝓝 (ENNReal.ofReal L)) := by
    convert ENNReal.tendsto_ofReal hlim using 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall (ha_pos n))).symm
  have he := tendsto_nhds_unique hmono ht
  refine ⟨hq, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hpos), he]
  exact ENNReal.ofReal_lt_top

/-- The positive real Gaussian is integrable in every finite-dimensional
real inner-product space. -/
theorem gaussian_real_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : V => Real.exp (- c⁻¹ * ‖x‖^2)) := by
  have hci : 0 < ((c : ℂ)⁻¹).re := by
    simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using inv_pos.mpr hc
  have hJ : Integrable (fun w : V => Complex.exp (- (c : ℂ)⁻¹ * ‖w‖^2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (c : ℂ)⁻¹) hci 0 (0 : V)
  convert hJ.re using 1
  ext x
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  rfl

/-- An everywhere nonnegative real Fourier transform is integrable if its
original L¹ function is continuous at zero. The integrability is derived
by Gaussian regularization and monotone convergence. -/
theorem integrable_nonnegative_fourier {f : V → ℂ} (hf : Integrable f)
    (hc : ContinuousAt f 0) {q : V → ℝ} (hpos : ∀ x, 0 ≤ q x)
    (heq : ∀ x, Real.fourierIntegral f x = (q x : ℂ)) : Integrable q := by
  have hF : Continuous (Real.fourierIntegral f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
  have hq : Continuous q := by
    convert Complex.continuous_re.comp hF using 1
    ext x
    change q x = (Real.fourierIntegral f x).re
    rw [heq]
    rfl
  have hb : ∃ C : ℝ, ∀ x : V, ‖q x‖ ≤ C := by
    refine ⟨∫ x : V, ‖f x‖, ?_⟩
    intro x
    have h := VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ V) f x
    change ‖Real.fourierIntegral f x‖ ≤ _ at h
    rw [heq] at h
    simpa only [Complex.norm_real] using h
  have hi (n : ℕ) : Integrable (fun x : V =>
      Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x) := by
    have h := (gaussian_real_integrable (V := V)
      (c := ((n+1 : ℕ) : ℝ)) (by positivity)).bdd_mul hq.aestronglyMeasurable hb
    simpa only [mul_comm] using h
  apply integrable_of_gaussian_integrals_tendsto hq.aestronglyMeasurable hpos hi
  have hseq : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    ((gaussian_regularized_fourier_limit hf hc).comp hseq)
  convert ht using 1
  ext n
  have hiC := (hi n).ofReal (𝕜 := ℂ)
  have he (x : V) :
      Complex.exp (- (((n+1 : ℕ) : ℂ))⁻¹ * ‖x‖^2) * Real.fourierIntegral f x =
        ((Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x : ℝ) : ℂ) := by
    rw [heq]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  dsimp only [Function.comp_apply]
  rw [← Complex.ofReal_re (∫ x : V, Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x)]
  congr 1
  calc
    _ = ∫ x : V, ((Real.exp (- (((n+1 : ℕ) : ℝ))⁻¹ * ‖x‖^2) * q x : ℝ) : ℂ) :=
      (integral_ofReal).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [Complex.ofReal_natCast] using (he x).symm

end WaringSiegel.WSL3
