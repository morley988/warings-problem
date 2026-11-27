import WaringSiegel.WSL3UnitSourceMeasure

/-!
# Continuous weighted densities and literal weighted trace transforms

The actual source image measures have L² densities whenever the source is
dominated by a positive box. Their real convolution is continuous, represents
the actual measure, and dominates the continuous inner-box density whenever
the source dominates that inner box.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
local instance : BorelSpace (mixedSpace K) := inferInstance
local instance : Measure.IsAddHaarMeasure (volume : Measure (mixedSpace K)) := inferInstance
local instance : IsLocallyFiniteMeasure (volume : Measure (mixedSpace K)) := inferInstance
local instance : SigmaCompactSpace (mixedSpace K) := inferInstance
local instance : Measure.Regular (volume : Measure (mixedSpace K)) := inferInstance
local instance : Measure.IsNegInvariant (volume : Measure (mixedSpace K)) := inferInstance

/-- The literal trace transform of the k-th power image of μ. -/
def sourceRootIntegral (k : ℕ) (μ : Measure (mixedSpace K)) (β : mixedSpace K) : ℂ :=
  ∫ x, archimedeanTraceCharacter β (x^k) ∂μ

theorem integrable_traceCharacter (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ]
    (β : mixedSpace K) : Integrable (archimedeanTraceCharacter β) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (archimedeanTraceCharacter_continuous β).aestronglyMeasurable
  exact Eventually.of_forall (fun x => (archimedeanTraceCharacter_norm β x).le)

theorem sourceRootIntegral_norm_le (k : ℕ) (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ]
    (β : mixedSpace K) : ‖sourceRootIntegral k μ β‖ ≤ (μ Set.univ).toReal := by
  unfold sourceRootIntegral
  calc
    _ ≤ ∫ x, ‖archimedeanTraceCharacter β (x^k)‖ ∂μ := norm_integral_le_integral_norm _
    _ = _ := by simp [archimedeanTraceCharacter_norm, Measure.real]

theorem sourceRootIntegral_continuous (k : ℕ) (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ] :
    Continuous (sourceRootIntegral k μ) := by
  apply continuous_iff_continuousAt.mpr
  intro β
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · exact Eventually.of_forall fun η =>
      ((archimedeanTraceCharacter_continuous η).comp (continuous_id.pow k)).aestronglyMeasurable
  · exact Eventually.of_forall fun η => Eventually.of_forall fun x => by
      rw [archimedeanTraceCharacter_norm]
  · exact integrable_const 1
  · exact Eventually.of_forall fun x => by
      have hc := (archimedeanTraceCharacter_continuous (x^k)).continuousAt (x := β)
      have he : (fun η : mixedSpace K => archimedeanTraceCharacter η (x^k)) =
          archimedeanTraceCharacter (x^k) :=
        funext (fun η => archimedeanTraceCharacter_symm η (x^k))
      rw [he]
      exact hc

/-- The Fourier product identity for the actual source convolution measure. -/
theorem sourceWaringMeasure_fourier (k s : ℕ) (μ : Measure (mixedSpace K)) [IsFiniteMeasure μ]
    (β : mixedSpace K) :
    (∫ x, archimedeanTraceCharacter β x ∂sourceWaringMeasure k μ s) =
      sourceRootIntegral k μ β ^ (s+1) := by
  have hzero : (∫ x, archimedeanTraceCharacter β x ∂sourceWaringMeasure k μ 0) =
      sourceRootIntegral k μ β := by
    have hp : Measurable (fun x : mixedSpace K => x^k) := (continuous_id.pow k).measurable
    rw [sourceWaringMeasure, integral_map hp.aemeasurable
      (archimedeanTraceCharacter_continuous β).aestronglyMeasurable]
    rfl
  induction s with
  | zero => simpa only [Nat.zero_add, pow_one] using hzero
  | succ s ih =>
      change (∫ x, archimedeanTraceCharacter β x ∂(sourceWaringMeasure k μ 0).conv
        (sourceWaringMeasure k μ s)) = _
      rw [integral_conv (integrable_traceCharacter _ β)]
      simp_rw [archimedeanTraceCharacter_add, integral_const_mul]
      rw [integral_mul_const, hzero, ih]
      ring

theorem sourceWaringDensity_fourier (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R))
    (β : mixedSpace K) :
    (∫ x, (sourceWaringDensity k s μ x).toReal • archimedeanTraceCharacter β x) =
      sourceRootIntegral k μ β ^ (s+1) :=
  (integral_rnDeriv_smul (sourceWaringMeasure_absolutelyContinuous k s hk ρ R hρ hμ)).trans
    (sourceWaringMeasure_fourier k s μ β)

/-- The genuine continuous density of s+2 weighted roots. -/
def sourceContinuousDensity (k s : ℕ) (μ : Measure (mixedSpace K)) (b : mixedSpace K) : ℝ :=
  ∫ x, (sourceWaringDensity k 0 μ x).toReal * (sourceWaringDensity k s μ (b-x)).toReal

theorem sourceContinuousDensity_nonneg (k s : ℕ) (μ : Measure (mixedSpace K)) (b : mixedSpace K) :
    0 ≤ sourceContinuousDensity k s μ b :=
  integral_nonneg (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

theorem sourceContinuousDensity_integrable (k s : ℕ) (μ : Measure (mixedSpace K))
    [IsFiniteMeasure μ] : Integrable (sourceContinuousDensity k s μ) :=
  (sourceWaringDensity_integrable k 0 μ).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (sourceWaringDensity_integrable k s μ)

theorem sourceContinuousDensity_continuous (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R)) :
    Continuous (sourceContinuousDensity k s μ) :=
  continuous_l2_convolution (sourceWaringDensity_memLp_two k 0 hk ρ R hρ hμ)
    (sourceWaringDensity_memLp_two k s hk ρ R hρ hμ)

theorem sourceContinuousDensity_measure (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R)) :
    volume.withDensity (fun b => ENNReal.ofReal (sourceContinuousDensity k s μ b)) =
      sourceWaringMeasure k μ (s+1) := by
  change _ = (sourceWaringMeasure k μ 0).conv (sourceWaringMeasure k μ s)
  rw [conv_eq_withDensity_lconvolution_rnDeriv
    (sourceWaringMeasure_absolutelyContinuous k 0 hk ρ R hρ hμ)
    (sourceWaringMeasure_absolutelyContinuous k s hk ρ R hρ hμ)]
  congr 1
  funext b
  rw [sourceContinuousDensity, ofReal_integral_eq_lintegral_ofReal
    (integrable_l2_convolution_integrand
      (sourceWaringDensity_memLp_two k 0 hk ρ R hρ hμ)
      (sourceWaringDensity_memLp_two k s hk ρ R hρ hμ) b)
    (Eventually.of_forall fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  apply lintegral_congr_ae
  filter_upwards [sourceWaringDensity_finite_ae k 0 μ,
    (Measure.measurePreserving_sub_left (volume : Measure (mixedSpace K)) b).quasiMeasurePreserving.ae
      (sourceWaringDensity_finite_ae k s μ)] with x hx hy
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hx.ne, ENNReal.ofReal_toReal hy.ne]
  simp only [sourceWaringDensity, sub_eq_neg_add]

theorem sourceContinuousDensity_ae_eq (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R)) :
    (fun x => (sourceWaringDensity k (s+1) μ x).toReal) =ᵐ[volume]
      sourceContinuousDensity k s μ := by
  have he := Measure.rnDeriv_withDensity (volume : Measure (mixedSpace K))
    (sourceContinuousDensity_continuous k s hk ρ R hρ hμ).measurable.ennreal_ofReal
  rw [sourceContinuousDensity_measure k s hk ρ R hρ hμ] at he
  filter_upwards [he] with x hx
  change ((sourceWaringMeasure k μ (s+1)).rnDeriv volume x).toReal = _
  rw [hx, ENNReal.toReal_ofReal (sourceContinuousDensity_nonneg k s μ x)]

theorem sourceContinuousDensity_fourier (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R))
    (β : mixedSpace K) :
    (∫ x, sourceContinuousDensity k s μ x • archimedeanTraceCharacter β x) =
      sourceRootIntegral k μ β ^ (s+2) := by
  calc
    _ = ∫ x, (sourceWaringDensity k (s+1) μ x).toReal • archimedeanTraceCharacter β x := by
      apply integral_congr_ae
      filter_upwards [sourceContinuousDensity_ae_eq k s hk ρ R hρ hμ] with x hx
      rw [hx]
    _ = _ := sourceWaringDensity_fourier k (s+1) hk ρ R hρ hμ β

/-- Domination of an inner source box gives domination of its actual density. -/
theorem sourceWaringDensity_ge_box (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R ρ' R' : ℝ) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hlo : volume.restrict (rootBox K ρ R) ≤ μ)
    (hhi : μ ≤ volume.restrict (rootBox K ρ' R')) :
    ∀ᵐ x ∂volume, (archimedeanWaringDensity k s ρ R x).toReal ≤
      (sourceWaringDensity k s μ x).toReal := by
  letI : IsFiniteMeasure (volume.restrict (rootBox K ρ R)) :=
    isFiniteMeasure_restrict.mpr (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  have hle := sourceWaringMeasure_mono k s hlo
  rw [sourceWaringMeasure_box] at hle
  have hden := rnDeriv_mono_of_absolutelyContinuous
    (archimedeanWaringMeasure_absolutelyContinuous k s hk ρ R hρ)
    (sourceWaringMeasure_absolutelyContinuous k s hk ρ' R' hρ' hhi) hle
  filter_upwards [hden, sourceWaringDensity_finite_ae k s μ] with x hx hxfin
  exact ENNReal.toReal_mono hxfin.ne hx

/-- A genuine pointwise density comparison, proved by positive convolution. -/
theorem sourceContinuousDensity_ge_box (k s : ℕ) (hk : 0 < k)
    {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
    (ρ R ρ' R' : ℝ) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hlo : volume.restrict (rootBox K ρ R) ≤ μ)
    (hhi : μ ≤ volume.restrict (rootBox K ρ' R')) (b : mixedSpace K) :
    continuousArchimedeanDensity k s ρ R b ≤ sourceContinuousDensity k s μ b := by
  apply integral_mono_ae
    (integrable_l2_convolution_integrand (archimedeanWaringDensity_memLp_two k 0 hk ρ R hρ)
      (archimedeanWaringDensity_memLp_two k s hk ρ R hρ) b)
    (integrable_l2_convolution_integrand (sourceWaringDensity_memLp_two k 0 hk ρ' R' hρ' hhi)
      (sourceWaringDensity_memLp_two k s hk ρ' R' hρ' hhi) b)
  filter_upwards [sourceWaringDensity_ge_box k 0 hk ρ R ρ' R' hρ hρ' hlo hhi,
    (Measure.measurePreserving_sub_left (volume : Measure (mixedSpace K)) b).quasiMeasurePreserving.ae
      (sourceWaringDensity_ge_box k s hk ρ R ρ' R' hρ hρ' hlo hhi)] with x hx hy
  exact mul_le_mul hx hy ENNReal.toReal_nonneg ENNReal.toReal_nonneg

end WaringSiegel.WSL3
