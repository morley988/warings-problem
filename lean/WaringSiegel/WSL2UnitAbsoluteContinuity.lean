import WaringSiegel.WSL2UnitConvolution

/-!
# Actual absolute continuity of the archimedean Waring measure

The positive root box is separated from every critical coordinate hyperplane.
The genuine Jacobian identity on finitely many injective charts proves that
its power-image measure is absolutely continuous. Fubini then proves the
same for the full sum-of-powers pushforward; no density assumption is used.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

/-- The actual real determinant never vanishes on the positive root box. -/
theorem mixedPowerDerivative_det_ne_zero (k : ℕ) (hk : 0 < k)
    (x : mixedSpace K) (hx : IsUnit x) : (mixedPowerDerivative k x).det ≠ 0 := by
  rw [← mixedPowerDerivativeEquiv_coe k hk x hx]
  exact (mixedPowerDerivativeEquiv k hk x hx).toLinearEquiv.isUnit_det'.ne_zero

/-- Nonvanishing Jacobian on an injective chart gives genuine absolute
continuity of the pushforward. -/
theorem power_chart_map_absolutelyContinuous (k : ℕ) (hk : 0 < k)
    {U : Set (mixedSpace K)} (hU : MeasurableSet U)
    (hunit : ∀ x ∈ U, IsUnit x) (hinj : Set.InjOn (fun x : mixedSpace K => x ^ k) U) :
    Measure.map (fun x : mixedSpace K => x ^ k) (volume.restrict U) ≪ volume := by
  let f : mixedSpace K → mixedSpace K := fun x => x ^ k
  let J : mixedSpace K → ENNReal := fun x => ENNReal.ofReal |(mixedPowerDerivative k x).det|
  have hJ : Measurable J :=
    ENNReal.continuous_ofReal.measurable.comp
      (ContinuousLinearMap.continuous_det.comp (continuous_mixedPowerDerivative k)).abs.measurable
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar volume hU.nullMeasurableSet
    (fun x _ => (hasFDerivAt_pow (𝕜 := ℝ) (x := x) k).hasFDerivWithinAt) hinj
  change Measure.map f ((volume.restrict U).withDensity J) = volume.restrict (f '' U) at hJac
  have hsource : volume.restrict U ≪ (volume.restrict U).withDensity J := by
    apply withDensity_absolutelyContinuous' hJ.aemeasurable
    filter_upwards [ae_restrict_mem hU] with x hx
    exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr
      (mixedPowerDerivative_det_ne_zero k hk x (hunit x hx)))).ne'
  have hmapped := hsource.map (show Measurable f from (continuous_id.pow k).measurable)
  rw [hJac] at hmapped
  exact hmapped.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- The power-image of the actual compact positive root box is absolutely
continuous with respect to Lebesgue measure. -/
theorem rootBox_power_map_absolutelyContinuous (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Measure.map (fun x : mixedSpace K => x ^ k) (volume.restrict (rootBox K ρ R)) ≪ volume := by
  let D := rootBox K ρ R
  have hD : MeasurableSet D := (rootBox_isCompact ρ R).measurableSet
  have hcharts (x : D) : ∃ U : Set (mixedSpace K), IsOpen U ∧ (x : mixedSpace K) ∈ U ∧
      Set.InjOn (fun z : mixedSpace K => z ^ k) U := by
    obtain ⟨U, hU, hx, -, hinj⟩ := exists_injective_mixed_power_chart (K := K) k hk (x : mixedSpace K) 0
      (rootBox_isUnit (K := K) hρ x.property) 1 zero_lt_one
    exact ⟨U, hU, hx, by simpa only [add_zero] using hinj⟩
  choose U hU hxU hinj using hcharts
  obtain ⟨T, hT⟩ := (rootBox_isCompact (K := K) ρ R).elim_finite_subcover U hU (by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hf : Measurable (fun x : mixedSpace K => x ^ k) := (continuous_id.pow k).measurable
  have hloc (j : D) : Measure.map (fun x : mixedSpace K => x ^ k)
      (volume.restrict (D ∩ U j)) ≪ volume :=
    power_chart_map_absolutelyContinuous (K := K) k hk (hD.inter (hU j).measurableSet)
      (fun x hx => rootBox_isUnit (K := K) hρ hx.1) ((hinj j).mono Set.inter_subset_right)
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hA0
  rw [Measure.map_apply hf hA,
    Measure.restrict_apply (hf hA)]
  have hnull (j : T) : volume ((fun x : mixedSpace K => x ^ k) ⁻¹' A ∩ (D ∩ U j)) = 0 := by
    have hj := hloc j.val hA0
    rwa [Measure.map_apply hf hA,
      Measure.restrict_apply (hf hA)] at hj
  apply measure_mono_null (t := ⋃ j : T, (fun x : mixedSpace K => x ^ k) ⁻¹' A ∩ (D ∩ U j))
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hT hx.2)
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx.1, hx.2, hxj⟩
  · exact measure_iUnion_null hnull

/-- Adding an arbitrary fixed shift preserves absolute continuity. -/
theorem rootBox_shifted_power_map_absolutelyContinuous (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (c : mixedSpace K) :
    Measure.map (fun x : mixedSpace K => x ^ k + c)
      (volume.restrict (rootBox K ρ R)) ≪ volume := by
  have hadd : Measurable (fun x : mixedSpace K => x + c) :=
    (continuous_id.add continuous_const).measurable
  have hpow : Measurable (fun x : mixedSpace K => x ^ k) := (continuous_id.pow k).measurable
  have h := (rootBox_power_map_absolutelyContinuous (K := K) k hk ρ R hρ).map hadd
  rw [Measure.map_map hadd hpow,
    Measure.IsAddRightInvariant.map_add_right_eq_self] at h
  exact h

/-- Every genuine full sum-of-powers measure from the fixed positive box
has a Lebesgue density. -/
theorem archimedeanWaringMeasure_absolutelyContinuous (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    archimedeanWaringMeasure (K := K) k s ρ R ≪ volume := by
  letI : BorelSpace (ArchimedeanTupleSpace K s) := inferInstance
  letI : SigmaFinite (volume : Measure (Fin s → mixedSpace K)) := by
    change SigmaFinite (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.sigmaFinite _
  have hf : Measurable (archimedeanWaringMap (K := K) k s) := by
    apply Continuous.measurable
    unfold archimedeanWaringMap
    fun_prop
  let D := rootBox K ρ R
  let T : Set (Fin s → mixedSpace K) := {y | ∀ i, y i ∈ D}
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hA0
  unfold archimedeanWaringMeasure
  rw [Measure.map_apply hf hA]
  change ((volume.prod volume).restrict (D ×ˢ T)) ((archimedeanWaringMap k s) ⁻¹' A) = 0
  rw [← Measure.prod_restrict, Measure.prod_apply_symm (hf hA)]
  have hz (y : Fin s → mixedSpace K) :
      (volume.restrict D) {x | archimedeanWaringMap k s (x, y) ∈ A} = 0 := by
    have h := rootBox_shifted_power_map_absolutelyContinuous (K := K) k hk ρ R hρ
      (∑ i, (y i) ^ k) hA0
    rwa [Measure.map_apply (by fun_prop) hA] at h
  change (∫⁻ y, (volume.restrict D) {x | archimedeanWaringMap k s (x, y) ∈ A}
    ∂volume.restrict T) = 0
  simp only [hz, lintegral_zero]

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.rootBox_power_map_absolutelyContinuous
#print axioms WaringSiegel.WSL2.archimedeanWaringMeasure_absolutelyContinuous
