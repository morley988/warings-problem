import WaringSiegel.WSL3UnitPowerLinearTail
import WaringSiegel.WSL3IdealPoissonPower

/-!
# Exact mixed-place factorization for every power degree with a linear twist

The actual fixed smooth source factors over all places, with the literal 2π
trace character and factor 2 Re at complex places. Every factor has arbitrary
rapid decay when the linear frequency dominates its power frequency.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
open WaringSiegel.WSL3Poisson
variable (k : ℕ)
set_option maxHeartbeats 800000

def realPlacePowerLinearKernel (rho R theta u x : ℝ) : ℂ :=
  (positiveSmoothWindow rho R x : ℂ) *
    Complex.exp (2*Real.pi*Complex.I*(theta*x^k+u*x : ℝ))

def complexPlacePowerLinearKernel (rho R : ℝ) (theta u z : ℂ) : ℂ :=
  (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) : ℂ) *
    Complex.exp (2*Real.pi*Complex.I*(2*(theta*z^k+u*z).re : ℝ))

def realPlacePowerLinearIntegral (rho R theta u : ℝ) : ℂ :=
  ∫ x : ℝ, realPlacePowerLinearKernel k rho R theta u x

def complexPlacePowerLinearIntegral (rho R : ℝ) (theta u : ℂ) : ℂ :=
  ∫ z : ℂ, complexPlacePowerLinearKernel k rho R theta u z

theorem realPlacePowerLinearIntegral_eq_rescaled (rho R theta u : ℝ) :
    realPlacePowerLinearIntegral k rho R theta u =
      smoothRealPowerLinearIntegral k rho R (2*Real.pi*theta) (2*Real.pi*u) := by
  apply integral_congr_ae
  filter_upwards [] with x
  unfold realPlacePowerLinearKernel
  congr 1
  congr 1
  push_cast
  ring

theorem complexPlacePowerLinearIntegral_eq_rescaled (rho R : ℝ) (theta u : ℂ) :
    complexPlacePowerLinearIntegral k rho R theta u =
      smoothComplexPowerLinearIntegral k rho R ((2*Real.pi:ℂ)*theta) ((2*Real.pi:ℂ)*u) := by
  apply integral_congr_ae
  filter_upwards [] with z
  unfold complexPlacePowerLinearKernel
  congr 1
  congr 1
  have he : (2*Real.pi:ℂ)*theta*z^k+(2*Real.pi:ℂ)*u*z =
      ((2*Real.pi:ℝ):ℂ)*(theta*z^k+u*z) := by push_cast; ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, mul_zero, sub_zero]
  push_cast
  ring

theorem realPlacePowerLinearKernel_norm (rho R theta u x : ℝ) :
    ‖realPlacePowerLinearKernel k rho R theta u x‖ = positiveSmoothWindow rho R x := by
  rw [realPlacePowerLinearKernel, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    zero_add, add_zero, sub_zero, zero_sub, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (positiveSmoothWindow_nonneg rho R x)]

theorem complexPlacePowerLinearKernel_norm (rho R : ℝ) (theta u z : ℂ) :
    ‖complexPlacePowerLinearKernel k rho R theta u z‖ =
      positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) := by
  simp [complexPlacePowerLinearKernel, norm_mul, Complex.norm_exp,
    abs_of_nonneg (positiveSmoothWindow_nonneg (rho^2) (R^2) (Complex.normSq z))]

theorem realPlacePowerLinearIntegral_tail (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      |theta| ≤ powerTailRadius k (2*R) * |u| →
      |u|^n * ‖realPlacePowerLinearIntegral k rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smooth_real_power_linear_nonstationary_bound k rho R hrho hR n
  refine ⟨C,hC,fun theta u ht => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have ht' : |2*Real.pi*theta| ≤ powerTailRadius k (2*R)*|2*Real.pi*u| := by
    rw [abs_mul (2*Real.pi) theta, abs_mul (2*Real.pi) u, abs_of_pos hp]
    nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
  have hu : |u| ≤ |2*Real.pi*u| := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [abs_nonneg u]
  rw [realPlacePowerLinearIntegral_eq_rescaled k]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg u) hu n) (norm_nonneg _)).trans
    (hb _ _ ht')

theorem complexPlacePowerLinearIntegral_tail (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ, 1 ≤ ‖u‖ →
      ‖theta‖ ≤ powerTailRadius k (2*R) * ‖u‖ →
      ‖u‖^n * ‖complexPlacePowerLinearIntegral k rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smooth_complex_power_linear_nonstationary_bound k rho R hrho hR n
  refine ⟨C,hC,fun theta u hu ht => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hn (z : ℂ) : ‖(2*Real.pi:ℂ)*z‖ = (2*Real.pi)*‖z‖ := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have ht' : ‖(2*Real.pi:ℂ)*theta‖ ≤ powerTailRadius k (2*R)*‖(2*Real.pi:ℂ)*u‖ := by
    simp only [hn]
    nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
  have huu : ‖u‖ ≤ ‖(2*Real.pi:ℂ)*u‖ := by rw [hn]; nlinarith [norm_nonneg u]
  rw [complexPlacePowerLinearIntegral_eq_rescaled k]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg u) huu n) (norm_nonneg _)).trans
    (hb _ _ (hu.trans huu) ht')

variable {K : Type*} [Field K] [NumberField K]

theorem powerLinearTracePhase_product (theta u x : mixedSpace K) :
    archimedeanTraceCharacter theta (x^k) * archimedeanTraceCharacter u x =
      (∏ w : {w : InfinitePlace K // IsReal w},
        Complex.exp (2*Real.pi*Complex.I*(theta.1 w*(x.1 w)^k+u.1 w*x.1 w : ℝ))) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        Complex.exp (2*Real.pi*Complex.I*(2*(theta.2 w*(x.2 w)^k+u.2 w*x.2 w).re : ℝ)) := by
  have he : archimedeanTraceCharacter theta (x^k) * archimedeanTraceCharacter u x =
      Complex.exp (2*Real.pi*Complex.I*(archimedeanTrace (theta*x^k+u*x) : ℂ)) := by
    rw [archimedeanTraceCharacter, archimedeanTraceCharacter, ← Complex.exp_add]
    congr 1
    rw [map_add, Complex.ofReal_add]
    ring
  rw [he, archimedeanTrace_eq_sum_real_complex]
  have hxr : (x^k).1 = fun w => (x.1 w)^k := rfl
  have hxc : (x^k).2 = fun w => (x.2 w)^k := rfl
  simp only [Prod.fst_add, Prod.fst_mul, Pi.add_apply, Pi.mul_apply,
    Prod.snd_add, Prod.snd_mul, hxr, hxc]
  have he' : 2*Real.pi*Complex.I*((
    (∑ w : {w : InfinitePlace K // IsReal w}, (theta.1 w*(x.1 w)^k+u.1 w*x.1 w)) +
      2*(∑ w, (theta.2 w*(x.2 w)^k+u.2 w*x.2 w).re) : ℝ) : ℂ) =
      (∑ w, 2*Real.pi*Complex.I*(theta.1 w*(x.1 w)^k+u.1 w*x.1 w : ℝ)) +
      ∑ w, 2*Real.pi*Complex.I*(2*(theta.2 w*(x.2 w)^k+u.2 w*x.2 w).re : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_ofNat, mul_add, Finset.mul_sum]
  rw [he', Complex.exp_add, Complex.exp_sum, Complex.exp_sum]

theorem smoothPowerLinearKernel_product (rho R : ℝ) (theta u x : mixedSpace K) :
    smoothRootWeight rho R x •
      (archimedeanTraceCharacter theta (x^k) * archimedeanTraceCharacter u x) =
      (∏ w : {w : InfinitePlace K // IsReal w}, realPlacePowerLinearKernel k rho R (theta.1 w) (u.1 w) (x.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlacePowerLinearKernel k rho R (theta.2 w) (u.2 w) (x.2 w) := by
  rw [powerLinearTracePhase_product k, Complex.real_smul, smoothRootWeight,
    Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  simp only [realPlacePowerLinearKernel, complexPlacePowerLinearKernel, Finset.prod_mul_distrib]
  ring

/-- Exact Fubini factorization, including the complex factor of two. -/
theorem smoothPowerLinearIntegral_product (rho R : ℝ) (theta u : mixedSpace K) :
    smoothPowerLinearIntegral k rho R theta u =
      (∏ w : {w : InfinitePlace K // IsReal w}, realPlacePowerLinearIntegral k rho R (theta.1 w) (u.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlacePowerLinearIntegral k rho R (theta.2 w) (u.2 w) := by
  calc
    _ = ∫ x : mixedSpace K,
        (∏ w : {w : InfinitePlace K // IsReal w}, realPlacePowerLinearKernel k rho R (theta.1 w) (u.1 w) (x.1 w)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlacePowerLinearKernel k rho R (theta.2 w) (u.2 w) (x.2 w) :=
      integral_congr_ae (Eventually.of_forall (smoothPowerLinearKernel_product k rho R theta u))
    _ = _ := by
      rw [Measure.volume_eq_prod, integral_prod_mul
        (fun xr : ({w : InfinitePlace K // IsReal w} → ℝ) =>
          ∏ w, realPlacePowerLinearKernel k rho R (theta.1 w) (u.1 w) (xr w))
        (fun xc : ({w : InfinitePlace K // IsComplex w} → ℂ) =>
          ∏ w, complexPlacePowerLinearKernel k rho R (theta.2 w) (u.2 w) (xc w)),
        integral_fintype_prod_volume_eq_prod,
        integral_fintype_prod_volume_eq_prod]
      rfl

#print axioms smoothPowerLinearIntegral_product
#print axioms realPlacePowerLinearIntegral_tail
#print axioms complexPlacePowerLinearIntegral_tail
end WaringSiegel.WSL3
