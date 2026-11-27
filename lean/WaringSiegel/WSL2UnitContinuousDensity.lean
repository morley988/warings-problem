import WaringSiegel.WSL2UnitLpDensity
import WaringSiegel.WSL2UnitMeasureRecursion
import WaringSiegel.WSL2UnitUniformDensity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Continuous densities from actual L² convolution

Translation is continuous in L². The L² inner product therefore gives a
continuous real convolution. The subsequent measure identity refers to
actual sum-of-powers image measures, not an assumed density representative.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

local instance : BorelSpace (mixedSpace K) := inferInstance
local instance : Measure.IsAddHaarMeasure (volume : Measure (mixedSpace K)) := inferInstance
local instance : IsLocallyFiniteMeasure (volume : Measure (mixedSpace K)) := inferInstance
local instance : SigmaCompactSpace (mixedSpace K) := inferInstance
local instance : Measure.Regular (volume : Measure (mixedSpace K)) := inferInstance
local instance : Measure.IsNegInvariant (volume : Measure (mixedSpace K)) := inferInstance

/-- Actual L² convolution on the mixed archimedean space is continuous. -/
theorem continuous_l2_convolution {f g : mixedSpace K → ℝ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    Continuous (fun b => ∫ x, f x * g (b - x)) := by
  let T : mixedSpace K → C(mixedSpace K, mixedSpace K) :=
    fun b => ⟨fun x => b - x, continuous_const.sub continuous_id⟩
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

/-- L² gives integrability at each individual convolution parameter. -/
theorem integrable_l2_convolution_integrand {f g : mixedSpace K → ℝ}
    (hf : MemLp f 2) (hg : MemLp g 2) (b : mixedSpace K) :
    Integrable (fun x => f x * g (b - x)) :=
  hf.integrable_mul (hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume b))

/-- The actual convolution of two previously constructed Waring densities. -/
def archimedeanBlockDensity (k s t : ℕ) (ρ R : ℝ) (b : mixedSpace K) : ℝ :=
  ∫ x, (archimedeanWaringDensity k s ρ R x).toReal *
    (archimedeanWaringDensity k t ρ R (b - x)).toReal

theorem archimedeanBlockDensity_continuous (k s t : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Continuous (archimedeanBlockDensity (K := K) k s t ρ R) :=
  continuous_l2_convolution
    (archimedeanWaringDensity_memLp_two k s hk ρ R hρ)
    (archimedeanWaringDensity_memLp_two k t hk ρ R hρ)

theorem archimedeanBlockDensity_nonneg (k s t : ℕ) (ρ R : ℝ) (b : mixedSpace K) :
    0 ≤ archimedeanBlockDensity k s t ρ R b :=
  integral_nonneg (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- The continuous convolution reconstructs the convolution of the actual
finite image measures. -/
theorem archimedeanBlockDensity_measure (k s t : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    volume.withDensity (fun b => ENNReal.ofReal (archimedeanBlockDensity k s t ρ R b)) =
      (archimedeanWaringMeasure (K := K) k s ρ R).conv
        (archimedeanWaringMeasure k t ρ R) := by
  rw [conv_eq_withDensity_lconvolution_rnDeriv
    (archimedeanWaringMeasure_absolutelyContinuous k s hk ρ R hρ)
    (archimedeanWaringMeasure_absolutelyContinuous k t hk ρ R hρ)]
  congr 1
  funext b
  rw [archimedeanBlockDensity, ofReal_integral_eq_lintegral_ofReal
    (integrable_l2_convolution_integrand
      (archimedeanWaringDensity_memLp_two k s hk ρ R hρ)
      (archimedeanWaringDensity_memLp_two k t hk ρ R hρ) b)
    (Eventually.of_forall fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  apply lintegral_congr_ae
  filter_upwards [archimedeanWaringDensity_finite_ae (K := K) k s ρ R,
    (Measure.measurePreserving_sub_left (volume : Measure (mixedSpace K)) b).quasiMeasurePreserving.ae
      (archimedeanWaringDensity_finite_ae (K := K) k t ρ R)] with x hx hy
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hx.ne, ENNReal.ofReal_toReal hy.ne]
  simp only [lconvolution, archimedeanWaringDensity, sub_eq_neg_add]

/-- A canonical continuous representative for s+2 actual root variables. -/
def continuousArchimedeanDensity (k s : ℕ) (ρ R : ℝ) : mixedSpace K → ℝ :=
  archimedeanBlockDensity k 0 s ρ R

theorem continuousArchimedeanDensity_continuous (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Continuous (continuousArchimedeanDensity (K := K) k s ρ R) :=
  archimedeanBlockDensity_continuous k 0 s hk ρ R hρ

theorem continuousArchimedeanDensity_nonneg (k s : ℕ) (ρ R : ℝ) (b : mixedSpace K) :
    0 ≤ continuousArchimedeanDensity k s ρ R b :=
  archimedeanBlockDensity_nonneg k 0 s ρ R b

/-- The continuous density belongs to the original literal s+2-variable
pushforward, by the proved first-coordinate product-measure recursion. -/
theorem continuousArchimedeanDensity_measure (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    volume.withDensity (fun b => ENNReal.ofReal (continuousArchimedeanDensity k s ρ R b)) =
      archimedeanWaringMeasure (K := K) k (s+1) ρ R := by
  rw [archimedeanWaringMeasure_succ]
  exact archimedeanBlockDensity_measure k 0 s hk ρ R hρ

theorem continuousArchimedeanDensity_ae_eq (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    (fun x : mixedSpace K => (archimedeanWaringDensity k (s+1) ρ R x).toReal) =ᵐ[volume]
      continuousArchimedeanDensity k s ρ R := by
  have he := Measure.rnDeriv_withDensity (volume : Measure (mixedSpace K))
    ((continuousArchimedeanDensity_continuous k s hk ρ R hρ).measurable.ennreal_ofReal)
  rw [continuousArchimedeanDensity_measure k s hk ρ R hρ] at he
  filter_upwards [he] with x hx
  change ((archimedeanWaringMeasure k (s+1) ρ R).rnDeriv volume x).toReal = _
  rw [hx, ENNReal.toReal_ofReal (continuousArchimedeanDensity_nonneg k s ρ R x)]

/-- A continuous density that is bounded below a.e. on an open set has the
same bound at every point there. -/
theorem continuous_lower_of_ae {f : mixedSpace K → ℝ} (hf : Continuous f)
    {c : ℝ} {U : Set (mixedSpace K)} (hU : IsOpen U)
    (h : ∀ᵐ x ∂volume.restrict U, c ≤ f x) : ∀ x ∈ U, c ≤ f x := by
  have he : (fun x => min c (f x)) =ᵐ[volume.restrict U] (fun _ => c) :=
    h.mono (fun _ hx => min_eq_left hx)
  have hp := Measure.eqOn_open_of_ae_eq he hU
    (continuous_const.min hf).continuousOn continuous_const.continuousOn
  intro x hx
  exact min_eq_left_iff.mp (hp hx)

/-- For any s+2 actual roots, one compact positive root box, one positive
constant and one positive radius work at every normalized target, pointwise.
No Fourier inversion or assumed continuous representative is used. -/
theorem exists_uniform_continuous_archimedean_density_lower
    (k s : ℕ) (hk : 0 < k) (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ IsCompact (rootBox K ρ R) ∧
      Continuous (continuousArchimedeanDensity (K := K) k s ρ R) ∧
      volume.withDensity (fun x : mixedSpace K => ENNReal.ofReal (continuousArchimedeanDensity k s ρ R x)) =
        archimedeanWaringMeasure (K := K) k (s+1) ρ R ∧
      ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ b ∈ compactTargetSet K B,
        ∀ x ∈ Metric.ball b δ, c ≤ continuousArchimedeanDensity k s ρ R x := by
  obtain ⟨ρ, R, hρ, hR, hcompact, c, δ, hc, hδ, hlower⟩ :=
    exists_uniform_archimedean_ball_density_lower (K := K) k (s+1) hk B hB
  refine ⟨ρ, R, hρ, hR, hcompact,
    continuousArchimedeanDensity_continuous k s hk ρ R hρ,
    continuousArchimedeanDensity_measure k s hk ρ R hρ, c, δ, hc, hδ, ?_⟩
  intro b hb
  apply continuous_lower_of_ae (continuousArchimedeanDensity_continuous k s hk ρ R hρ)
    Metric.isOpen_ball
  filter_upwards [hlower b hb, ae_restrict_of_ae (continuousArchimedeanDensity_ae_eq k s hk ρ R hρ)]
    with x hx he
  rwa [he] at hx

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.continuousArchimedeanDensity_measure
#print axioms WaringSiegel.WSL2.exists_uniform_continuous_archimedean_density_lower
