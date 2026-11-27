import WaringSiegel.WSL3UnitComplexCubicTail
import WaringSiegel.WSL3UnitSmoothSchwartz
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact place factorization of the smooth cubic trace integral

The factors carry the literal 2π trace character. The complex factor uses
2 Re, and the product uses ordinary real/complex product Lebesgue volume.
The identities and estimates apply to the actual fixed smooth product weight.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
set_option maxHeartbeats 800000

def realPlaceCubicKernel (rho R theta u x : ℝ) : ℂ :=
  (positiveSmoothWindow rho R x : ℂ) *
    Complex.exp (2*Real.pi*Complex.I*(theta*x^3+u*x : ℝ))

def complexPlaceCubicKernel (rho R : ℝ) (theta u z : ℂ) : ℂ :=
  (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) : ℂ) *
    Complex.exp (2*Real.pi*Complex.I*(2*(theta*z^3+u*z).re : ℝ))

def realPlaceCubicIntegral (rho R theta u : ℝ) : ℂ :=
  ∫ x : ℝ, realPlaceCubicKernel rho R theta u x

def complexPlaceCubicIntegral (rho R : ℝ) (theta u : ℂ) : ℂ :=
  ∫ z : ℂ, complexPlaceCubicKernel rho R theta u z

theorem realPlaceCubicIntegral_eq_rescaled (rho R theta u : ℝ) :
    realPlaceCubicIntegral rho R theta u =
      smoothRealCubicIntegral rho R (2*Real.pi*theta) (2*Real.pi*u) := by
  apply integral_congr_ae
  filter_upwards [] with x
  unfold realPlaceCubicKernel
  congr 1
  congr 1
  push_cast
  ring

theorem complexPlaceCubicIntegral_eq_rescaled (rho R : ℝ) (theta u : ℂ) :
    complexPlaceCubicIntegral rho R theta u =
      smoothComplexCubicIntegral rho R ((2*Real.pi:ℂ)*theta) ((2*Real.pi:ℂ)*u) := by
  apply integral_congr_ae
  filter_upwards [] with z
  unfold complexPlaceCubicKernel
  congr 1
  congr 1
  have he : (2*Real.pi:ℂ)*theta*z^3+(2*Real.pi:ℂ)*u*z =
      ((2*Real.pi:ℝ):ℂ)*(theta*z^3+u*z) := by push_cast; ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, mul_zero, sub_zero]
  push_cast
  ring

theorem realPlaceCubicKernel_norm (rho R theta u x : ℝ) :
    ‖realPlaceCubicKernel rho R theta u x‖ = positiveSmoothWindow rho R x := by
  rw [realPlaceCubicKernel, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    zero_add, add_zero, sub_zero, zero_sub, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (positiveSmoothWindow_nonneg rho R x)]

theorem complexPlaceCubicKernel_norm (rho R : ℝ) (theta u z : ℂ) :
    ‖complexPlaceCubicKernel rho R theta u z‖ =
      positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) := by
  simp [complexPlaceCubicKernel, norm_mul, Complex.norm_exp,
    abs_of_nonneg (positiveSmoothWindow_nonneg (rho^2) (R^2) (Complex.normSq z))]

theorem realPlaceCubicIntegral_tail (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      |theta| ≤ cubicTailRadius (2*R) * |u| →
      |u|^n * ‖realPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smooth_real_cubic_nonstationary_bound rho R hrho hR n
  refine ⟨C,hC,fun theta u ht => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have ht' : |2*Real.pi*theta| ≤ cubicTailRadius (2*R)*|2*Real.pi*u| := by
    rw [abs_mul (2*Real.pi) theta, abs_mul (2*Real.pi) u, abs_of_pos hp]
    nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
  have hu : |u| ≤ |2*Real.pi*u| := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [abs_nonneg u]
  rw [realPlaceCubicIntegral_eq_rescaled]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg u) hu n) (norm_nonneg _)).trans
    (hb _ _ ht')

theorem complexPlaceCubicIntegral_tail (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ, 1 ≤ ‖u‖ →
      ‖theta‖ ≤ cubicTailRadius (2*R) * ‖u‖ →
      ‖u‖^n * ‖complexPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smooth_complex_cubic_nonstationary_bound rho R hrho hR n
  refine ⟨C,hC,fun theta u hu ht => ?_⟩
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hn (z : ℂ) : ‖(2*Real.pi:ℂ)*z‖ = (2*Real.pi)*‖z‖ := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have ht' : ‖(2*Real.pi:ℂ)*theta‖ ≤ cubicTailRadius (2*R)*‖(2*Real.pi:ℂ)*u‖ := by
    simp only [hn]
    nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
  have huu : ‖u‖ ≤ ‖(2*Real.pi:ℂ)*u‖ := by rw [hn]; nlinarith [norm_nonneg u]
  rw [complexPlaceCubicIntegral_eq_rescaled]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg u) huu n) (norm_nonneg _)).trans
    (hb _ _ (hu.trans huu) ht')

variable {K : Type*} [Field K] [NumberField K]

/-- The literal mixed-space cubic integral with an arbitrary linear twist. -/
def smoothCubicLinearIntegral (rho R : ℝ) (theta u : mixedSpace K) : ℂ :=
  ∫ x, smoothRootWeight rho R x •
    (archimedeanTraceCharacter theta (x^3) * archimedeanTraceCharacter u x)

theorem cubicTracePhase_product (theta u x : mixedSpace K) :
    archimedeanTraceCharacter theta (x^3) * archimedeanTraceCharacter u x =
      (∏ w : {w : InfinitePlace K // IsReal w},
        Complex.exp (2*Real.pi*Complex.I*(theta.1 w*(x.1 w)^3+u.1 w*x.1 w : ℝ))) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        Complex.exp (2*Real.pi*Complex.I*(2*(theta.2 w*(x.2 w)^3+u.2 w*x.2 w).re : ℝ)) := by
  have he : archimedeanTraceCharacter theta (x^3) * archimedeanTraceCharacter u x =
      Complex.exp (2*Real.pi*Complex.I*(archimedeanTrace (theta*x^3+u*x) : ℂ)) := by
    rw [archimedeanTraceCharacter, archimedeanTraceCharacter, ← Complex.exp_add]
    congr 1
    rw [map_add, Complex.ofReal_add]
    ring
  rw [he, archimedeanTrace_eq_sum_real_complex]
  have hxr : (x^3).1 = fun w => (x.1 w)^3 := rfl
  have hxc : (x^3).2 = fun w => (x.2 w)^3 := rfl
  simp only [Prod.fst_add, Prod.fst_mul, Pi.add_apply, Pi.mul_apply,
    Prod.snd_add, Prod.snd_mul, hxr, hxc]
  have he' : 2*Real.pi*Complex.I*((
    (∑ w : {w : InfinitePlace K // IsReal w}, (theta.1 w*(x.1 w)^3+u.1 w*x.1 w)) +
      2*(∑ w, (theta.2 w*(x.2 w)^3+u.2 w*x.2 w).re) : ℝ) : ℂ) =
      (∑ w, 2*Real.pi*Complex.I*(theta.1 w*(x.1 w)^3+u.1 w*x.1 w : ℝ)) +
      ∑ w, 2*Real.pi*Complex.I*(2*(theta.2 w*(x.2 w)^3+u.2 w*x.2 w).re : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_ofNat, mul_add, Finset.mul_sum]
  rw [he', Complex.exp_add, Complex.exp_sum, Complex.exp_sum]

theorem smoothCubicLinearKernel_product (rho R : ℝ) (theta u x : mixedSpace K) :
    smoothRootWeight rho R x •
      (archimedeanTraceCharacter theta (x^3) * archimedeanTraceCharacter u x) =
      (∏ w : {w : InfinitePlace K // IsReal w}, realPlaceCubicKernel rho R (theta.1 w) (u.1 w) (x.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlaceCubicKernel rho R (theta.2 w) (u.2 w) (x.2 w) := by
  rw [cubicTracePhase_product, Complex.real_smul, smoothRootWeight,
    Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  simp only [realPlaceCubicKernel, complexPlaceCubicKernel, Finset.prod_mul_distrib]
  ring

/-- Exact Fubini factorization, including the complex factor of two. -/
theorem smoothCubicLinearIntegral_product (rho R : ℝ) (theta u : mixedSpace K) :
    smoothCubicLinearIntegral rho R theta u =
      (∏ w : {w : InfinitePlace K // IsReal w}, realPlaceCubicIntegral rho R (theta.1 w) (u.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlaceCubicIntegral rho R (theta.2 w) (u.2 w) := by
  calc
    _ = ∫ x : mixedSpace K,
        (∏ w : {w : InfinitePlace K // IsReal w}, realPlaceCubicKernel rho R (theta.1 w) (u.1 w) (x.1 w)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlaceCubicKernel rho R (theta.2 w) (u.2 w) (x.2 w) :=
      integral_congr_ae (Eventually.of_forall (smoothCubicLinearKernel_product rho R theta u))
    _ = _ := by
      rw [Measure.volume_eq_prod, integral_prod_mul
        (fun xr : ({w : InfinitePlace K // IsReal w} → ℝ) =>
          ∏ w, realPlaceCubicKernel rho R (theta.1 w) (u.1 w) (xr w))
        (fun xc : ({w : InfinitePlace K // IsComplex w} → ℂ) =>
          ∏ w, complexPlaceCubicKernel rho R (theta.2 w) (u.2 w) (xc w)),
        integral_fintype_prod_volume_eq_prod,
        integral_fintype_prod_volume_eq_prod]
      rfl

#print axioms smoothCubicLinearIntegral_product
#print axioms realPlaceCubicIntegral_tail
#print axioms complexPlaceCubicIntegral_tail
end WaringSiegel.WSL3
