import WaringSiegel.WSL3UnitGaussianIntegrability
import WaringSiegel.WSL3UnitFourierConvolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Genuine square-integrability of the Fourier transform of an L¹∩L² density

The real autocorrelation is continuous by L² translation continuity and
integrable by Fubini. Its transform is the squared modulus of the original
transform. Gaussian regularization and monotone convergence therefore prove
frequency integrability; no Plancherel theorem is assumed.
-/
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped FourierTransform RealInnerProductSpace Convolution
namespace WaringSiegel.WSL3
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 800000

theorem continuous_l2_convolution_euclidean {f g : V → ℝ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    Continuous (fun b => ∫ x : V, f x * g (b-x)) := by
  let T : V → C(V, V) := fun b => ⟨fun x => b-x, continuous_const.sub continuous_id⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T
    (continuous_fst.sub continuous_snd)
  have hTm : ∀ b, MeasurePreserving (T b) :=
    fun b => Measure.measurePreserving_sub_left volume b
  have hc : Continuous (fun b => Lp.compMeasurePreserving (T b) (hTm b) (hg.toLp g)) :=
    continuous_const.compMeasurePreservingLp hT hTm (by norm_num)
  have hi : Continuous (fun b => inner ℝ (hf.toLp f)
      (Lp.compMeasurePreserving (T b) (hTm b) (hg.toLp g))) := continuous_const.inner hc
  convert hi using 1
  ext b
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, Lp.coeFn_compMeasurePreserving (hg.toLp g) (hTm b),
    (hTm b).quasiMeasurePreserving.ae hg.coeFn_toLp] with x hfx htx hgx
  simp only [Function.comp_apply] at htx hgx
  rw [hfx, htx, hgx]
  simp [T, mul_comm]

theorem fourier_real_reflection (f : V → ℝ) (ξ : V) :
    Real.fourierIntegral (fun x : V => (f (-x) : ℂ)) ξ =
      starRingEnd ℂ (Real.fourierIntegral (fun x : V => (f x : ℂ)) ξ) := by
  have h := Real.fourierIntegral_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ (E := V)) (fun x : V => (f x : ℂ)) ξ
  change Real.fourierIntegral (fun x : V => (f (-x) : ℂ)) ξ =
    Real.fourierIntegral (fun x : V => (f x : ℂ)) (-ξ) at h
  rw [h, Real.fourierIntegral_eq', Real.fourierIntegral_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, inner_neg_right, Complex.ofReal_neg]
  congr 2
  push_cast
  ring

def realAutocorrelation (f : V → ℝ) (x : V) : ℝ :=
  ∫ y : V, f y * f (-(x-y))

theorem realAutocorrelation_integrable {f : V → ℝ} (hf : Integrable f) :
    Integrable (realAutocorrelation f) :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.comp_neg

theorem realAutocorrelation_continuous {f : V → ℝ} (hf : MemLp f 2) :
    Continuous (realAutocorrelation f) :=
  continuous_l2_convolution_euclidean hf
    (hf.comp_measurePreserving (Measure.measurePreserving_neg volume))

theorem fourier_realAutocorrelation {f : V → ℝ} (hf : Integrable f) (ξ : V) :
    Real.fourierIntegral (fun x : V => (realAutocorrelation f x : ℂ)) ξ =
      ((‖Real.fourierIntegral (fun x : V => (f x : ℂ)) ξ‖^2 : ℝ) : ℂ) := by
  have hc : (fun x : V => (realAutocorrelation f x : ℂ)) =
      (fun x : V => ∫ y : V, (f y : ℂ) * (f (-(x-y)) : ℂ)) := by
    funext x
    change (↑(∫ y : V, f y * f (-(x-y))) : ℂ) = _
    calc
      _ = ∫ y : V, ((f y * f (-(x-y)) : ℝ) : ℂ) := (integral_ofReal).symm
      _ = _ := by simp only [Complex.ofReal_mul]
  rw [hc]
  calc
    _ = Real.fourierIntegral (fun x : V => (f x : ℂ)) ξ *
        Real.fourierIntegral (fun x : V => (f (-x) : ℂ)) ξ :=
      fourier_integrable_convolution (f := fun x : V => (f x : ℂ))
        (g := fun x : V => (f (-x) : ℂ)) hf.ofReal hf.comp_neg.ofReal ξ
    _ = _ := by rw [fourier_real_reflection, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The actual Fourier transform of every real L¹∩L² function has an
integrable squared modulus, derived by the autocorrelation argument. -/
theorem fourier_norm_sq_integrable_real {f : V → ℝ}
    (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun ξ : V => ‖Real.fourierIntegral (fun x : V => (f x : ℂ)) ξ‖^2) := by
  exact integrable_nonnegative_fourier (realAutocorrelation_integrable hf).ofReal
    (Complex.continuous_ofReal.comp (realAutocorrelation_continuous h2)).continuousAt
    (fun _ => sq_nonneg _) (fourier_realAutocorrelation hf)

end WaringSiegel.WSL3
