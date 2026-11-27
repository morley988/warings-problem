import WaringSiegel.WSL2UnitCharts
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# A genuine archimedean pushforward-volume lower bound

The actual first-variable power map has an invertible derivative at every
mixed unit. Change of variables on its injective local chart, together with
a uniform Jacobian bound on the compact root box, gives domination of local
Lebesgue measure by the actual pushforward of root-box volume.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- Scalar multiplication preserves the order on actual measures. -/
theorem measure_smul_mono {X : Type*} [MeasurableSpace X] (c : ENNReal)
    {μ ν : Measure X} (h : μ ≤ ν) : c • μ ≤ c • ν := by
  apply Measure.le_iff.mpr
  intro S hS
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left' (Measure.le_iff.mp h S hS) c

def mixedPowerDerivative (k : ℕ) (x : mixedSpace K) : mixedSpace K →L[ℝ] mixedSpace K :=
  (k • x ^ (k - 1)) • ContinuousLinearMap.id ℝ (mixedSpace K)

theorem mixedPowerDerivative_bijective (k : ℕ) (hk : 0 < k)
    (a : mixedSpace K) (ha : IsUnit a) : Function.Bijective (mixedPowerDerivative k a) :=
  IsUnit.isUnit_iff_mulLeft_bijective.mp (mixed_pow_derivative_isUnit k hk a ha)

def mixedPowerDerivativeEquiv (k : ℕ) (hk : 0 < k)
    (a : mixedSpace K) (ha : IsUnit a) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  ContinuousLinearEquiv.ofBijective (mixedPowerDerivative k a)
    (LinearMap.ker_eq_bot.mpr (mixedPowerDerivative_bijective k hk a ha).injective)
    (LinearMap.range_eq_top.mpr (mixedPowerDerivative_bijective k hk a ha).surjective)

theorem mixedPowerDerivativeEquiv_coe (k : ℕ) (hk : 0 < k)
    (a : mixedSpace K) (ha : IsUnit a) :
    (mixedPowerDerivativeEquiv k hk a ha : mixedSpace K →L[ℝ] mixedSpace K) =
      mixedPowerDerivative k a := ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem continuous_mixedPowerDerivative (k : ℕ) :
    Continuous (mixedPowerDerivative (K := K) k) := by
  have he : mixedPowerDerivative (K := K) k = fun x =>
      ContinuousLinearMap.mul ℝ (mixedSpace K) (k • x ^ (k - 1)) := by
    funext x
    apply ContinuousLinearMap.ext
    intro y
    rfl
  rw [he]
  exact (ContinuousLinearMap.mul ℝ (mixedSpace K)).continuous.comp
    ((continuous_id.pow (k - 1)).nsmul k)

/-- One finite positive Jacobian bound works on the entire fixed root box. -/
theorem exists_rootBox_jacobian_bound (k : ℕ) (ρ R : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ rootBox K ρ R,
      |(mixedPowerDerivative k x).det| ≤ M := by
  have hc : Continuous (fun x : mixedSpace K => |(mixedPowerDerivative k x).det|) :=
    (ContinuousLinearMap.continuous_det.comp (continuous_mixedPowerDerivative k)).abs
  obtain ⟨M, hM, hb⟩ := ((rootBox_isCompact (K := K) ρ R).image hc).isBounded.exists_pos_norm_le
  refine ⟨M, hM, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_abs] using hb _ (Set.mem_image_of_mem _ hx)

/-- There is an actual injective open power chart in every prescribed
neighborhood of a mixed unit. -/
theorem exists_injective_mixed_power_chart (k : ℕ) (hk : 0 < k)
    (a c : mixedSpace K) (ha : IsUnit a) (r : ℝ) (hr : 0 < r) :
    ∃ U : Set (mixedSpace K), IsOpen U ∧ a ∈ U ∧ U ⊆ Metric.ball a r ∧
      Set.InjOn (fun x : mixedSpace K => x ^ k + c) U := by
  let f : mixedSpace K → mixedSpace K := fun x => x ^ k + c
  let e := mixedPowerDerivativeEquiv k hk a ha
  have hder : HasStrictFDerivAt f (e : mixedSpace K →L[ℝ] mixedSpace K) a := by
    rw [mixedPowerDerivativeEquiv_coe]
    exact (hasStrictFDerivAt_pow (𝕜 := ℝ) (x := a) k).add_const c
  let H := hder.toOpenPartialHomeomorph f
  refine ⟨H.source ∩ Metric.ball a r, H.open_source.inter Metric.isOpen_ball,
    ⟨hder.mem_toOpenPartialHomeomorph_source, Metric.mem_ball_self hr⟩, Set.inter_subset_right, ?_⟩
  exact H.injOn.mono Set.inter_subset_left

/-- Change of variables makes the Jacobian bound an actual measure domination
statement for the pushforward of root-box volume. -/
theorem local_chart_volume_domination (k : ℕ) (c : mixedSpace K) (ρ R M : ℝ)
    (hM : ∀ x ∈ rootBox K ρ R, |(mixedPowerDerivative k x).det| ≤ M)
    {U : Set (mixedSpace K)} (hU : MeasurableSet U) (hsub : U ⊆ rootBox K ρ R)
    (hinj : Set.InjOn (fun x : mixedSpace K => x ^ k + c) U) :
    volume.restrict ((fun x : mixedSpace K => x ^ k + c) '' U) ≤
      ENNReal.ofReal M • Measure.map (fun x : mixedSpace K => x ^ k + c)
        (volume.restrict (rootBox K ρ R)) := by
  let f : mixedSpace K → mixedSpace K := fun x => x ^ k + c
  have hf : Measurable f := (by fun_prop : Continuous f).measurable
  have hjac := map_withDensity_abs_det_fderiv_eq_addHaar volume hU.nullMeasurableSet
    (fun x _ => ((hasFDerivAt_pow (𝕜 := ℝ) (x := x) k).add_const c).hasFDerivWithinAt) hinj
  have hden : (volume.restrict U).withDensity
      (fun x => ENNReal.ofReal |(mixedPowerDerivative k x).det|) ≤
      ENNReal.ofReal M • volume.restrict U := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hU] with x hx
    exact ENNReal.ofReal_le_ofReal (hM x (hsub hx))
  calc
    volume.restrict (f '' U) = Measure.map f ((volume.restrict U).withDensity
        (fun x => ENNReal.ofReal |(mixedPowerDerivative k x).det|)) := hjac.symm
    _ ≤ Measure.map f (ENNReal.ofReal M • volume.restrict U) := Measure.map_mono hden hf
    _ = ENNReal.ofReal M • Measure.map f (volume.restrict U) := Measure.map_smul _ _ _
    _ ≤ ENNReal.ofReal M • Measure.map f (volume.restrict (rootBox K ρ R)) := by
      exact measure_smul_mono (ENNReal.ofReal M)
        (Measure.map_mono (Measure.restrict_mono hsub le_rfl) hf)

/-- The constant precedes every center and translation. Each actual nonsingular
anchor gives local Lebesgue domination by the actual power-image measure. -/
theorem exists_uniform_local_power_volume_bound (k : ℕ) (hk : 0 < k) (ρ R : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ a c : mixedSpace K, IsUnit a → ∀ r : ℝ, 0 < r →
      Metric.closedBall a r ⊆ rootBox K ρ R →
      ∃ V : Set (mixedSpace K), IsOpen V ∧ a ^ k + c ∈ V ∧
        volume.restrict V ≤ ENNReal.ofReal M •
          Measure.map (fun x : mixedSpace K => x ^ k + c) (volume.restrict (rootBox K ρ R)) := by
  obtain ⟨M, hM, hb⟩ := exists_rootBox_jacobian_bound (K := K) k ρ R
  refine ⟨M, hM, ?_⟩
  intro a c hau r hr hball
  obtain ⟨U, hU, haU, hUball, hinj⟩ := exists_injective_mixed_power_chart k hk a c hau r hr
  let V := interior ((fun x : mixedSpace K => x ^ k + c) '' U)
  refine ⟨V, isOpen_interior, ?_, ?_⟩
  · exact mem_interior_iff_mem_nhds.mpr
      (shifted_mixed_pow_image_mem_nhds k hk a c hau (hU.mem_nhds haU))
  · exact (Measure.restrict_mono interior_subset le_rfl).trans
      (local_chart_volume_domination k c ρ R M hb hU.measurableSet
        (hUball.trans (Metric.ball_subset_closedBall.trans hball)) hinj)

/-- A general Jacobian upper bound on an injective chart yields domination
of image volume by the pushforward of the surrounding domain's volume. -/
theorem measure_domination_of_jacobian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (f' : E → E →L[ℝ] E) (hf : Measurable f)
    (D : Set E) (M : ℝ) (hM : ∀ x ∈ D, |(f' x).det| ≤ M)
    {U : Set E} (hU : MeasurableSet U) (hsub : U ⊆ D)
    (hder : ∀ x ∈ U, HasFDerivWithinAt f (f' x) U x) (hinj : Set.InjOn f U) :
    μ.restrict (f '' U) ≤ ENNReal.ofReal M • Measure.map f (μ.restrict D) := by
  have hjac := map_withDensity_abs_det_fderiv_eq_addHaar μ hU.nullMeasurableSet hder hinj
  have hden : (μ.restrict U).withDensity (fun x => ENNReal.ofReal |(f' x).det|) ≤
      ENNReal.ofReal M • μ.restrict U := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hU] with x hx
    exact ENNReal.ofReal_le_ofReal (hM x (hsub hx))
  calc
    μ.restrict (f '' U) = Measure.map f ((μ.restrict U).withDensity
        (fun x => ENNReal.ofReal |(f' x).det|)) := hjac.symm
    _ ≤ Measure.map f (ENNReal.ofReal M • μ.restrict U) := Measure.map_mono hden hf
    _ = ENNReal.ofReal M • Measure.map f (μ.restrict U) := Measure.map_smul _ _ _
    _ ≤ ENNReal.ofReal M • Measure.map f (μ.restrict D) :=
      measure_smul_mono (ENNReal.ofReal M)
        (Measure.map_mono (Measure.restrict_mono hsub le_rfl) hf)

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_uniform_local_power_volume_bound
