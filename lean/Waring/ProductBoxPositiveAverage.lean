import Waring.ProductBoxGaussianLower

/-! # Positive Fourier densities from a genuine interval variable -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Waring.ProductBox

theorem gaussianMass_le {T : ℝ} (hT : 0≤T) (h : ℝ) :
    gaussianMass T h≤T*Real.pi^(1/2 : ℝ) := by
  unfold gaussianMass
  calc
    _ ≤ T*Real.pi^(1/2 : ℝ)*1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_one_iff.mpr
      have : 0≤Real.pi^2*T^2*h^2 := by positivity
      linarith
    _ = _ := mul_one _

theorem integrable_gaussianMass_comp {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν] (h : Y → ℝ)
    (hh : Continuous h) {T : ℝ} (hT : 0≤T) :
    Integrable (fun y => gaussianMass T (h y)) ν := by
  apply (integrable_const (T*Real.pi^(1/2 : ℝ))).mono'
    ((continuous_gaussianMass T).comp hh).aestronglyMeasurable
  filter_upwards with y
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (gaussianMass_nonneg hT _)]
  exact gaussianMass_le hT _

/-- A positive-measure set of remaining variables gives a uniform lower bound.
The average and its Fourier integral are literal Lebesgue integrals. -/
theorem centeredAverage_integral_lower {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (h : Y → ℝ) (hh : Continuous h)
    {k : ℕ} (hk : 0<k) {b θ : ℝ} (hb0 : 0≤b) (hb1 : b<1)
    (B : Set Y) (hB : MeasurableSet B)
    (hwindow : ∀ y∈B,θ-h y∈Set.Icc 0 b)
    (hFourier : Integrable (centeredAverage (ν.prod unitIntervalMeasure)
      (fun z : Y×ℝ => z.2^k+h z.1) θ)) :
    monomialGaussianConstant k*ν.real B≤
      (∫ β : ℝ,centeredAverage (ν.prod unitIntervalMeasure)
        (fun z : Y×ℝ => z.2^k+h z.1) θ β).re := by
  let H : Y×ℝ → ℝ := fun z => z.2^k+h z.1
  have hH : Continuous H := (continuous_snd.pow k).add (hh.comp continuous_fst)
  have ht := tendsto_gaussian_damping_integral hFourier
  have htre := Complex.continuous_re.continuousAt.tendsto.comp ht
  apply ge_of_tendsto htre
  obtain ⟨T0,hT0,huniform⟩ := gaussian_monomial_uniform hk hb0 hb1
  filter_upwards [eventually_ge_atTop T0] with T hT
  have hTp : 0<T := hT0.trans_le hT
  have hident := gaussian_average_identity (ν.prod unitIntervalMeasure) H hH hTp θ
  change (∫ β : ℝ,(gaussianDamping T β : ℂ)*
    centeredAverage (ν.prod unitIntervalMeasure) H θ β)=
      ∫ z,((gaussianMass T (H z-θ)) : ℂ) ∂ν.prod unitIntervalMeasure at hident
  change monomialGaussianConstant k*ν.real B≤
    (∫ β : ℝ,(gaussianDamping T β : ℂ)*centeredAverage
      (ν.prod unitIntervalMeasure) H θ β).re
  rw [hident,integral_complex_ofReal,Complex.ofReal_re]
  have hi := integrable_gaussianMass_comp (ν.prod unitIntervalMeasure)
    (fun z => H z-θ) (hH.sub continuous_const) hTp.le
  rw [integral_prod _ hi]
  let G : Y → ℝ := fun y => ∫ t,gaussianMass T (t^k+h y-θ) ∂unitIntervalMeasure
  have hGi : Integrable G ν := hi.integral_prod_left
  have hGnonneg : ∀ y,0≤G y := by
    intro y
    apply integral_nonneg
    intro t
    exact gaussianMass_nonneg hTp.le _
  have hpoint (y : Y) (hy : y∈B) : monomialGaussianConstant k≤G y := by
    have hl := huniform T hT (θ-h y) (hwindow y hy)
    convert hl using 1
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    ring
  have hsmall := setIntegral_ge_of_const_le hB (measure_ne_top ν B) hpoint
    hGi.integrableOn
  exact hsmall.trans (integral_mono_measure ν.restrict_le_self
    (Filter.Eventually.of_forall hGnonneg) hGi)

#print axioms centeredAverage_integral_lower
end Waring.ProductBox
