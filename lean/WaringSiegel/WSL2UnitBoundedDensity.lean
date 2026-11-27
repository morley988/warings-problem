import WaringSiegel.WSL2UnitDensity

/-!
# An actual bounded archimedean Waring density

The power-map Jacobian has a positive minimum on the compact root box.
A finite cover by genuine injective charts gives a global Lebesgue upper
bound for the image measure. Translation and Fubini carry the same bound to
the full sum-of-powers measure, proving an actual essential density bound.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

/-- The actual determinant is uniformly separated from zero on the fixed
positive root box. -/
theorem exists_rootBox_jacobian_lower (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ rootBox K ρ R, m ≤ |(mixedPowerDerivative k x).det| := by
  apply (rootBox_isCompact (K := K) ρ R).exists_forall_le'
    ((ContinuousLinearMap.continuous_det.comp (continuous_mixedPowerDerivative k)).abs.continuousOn)
  intro x hx
  exact abs_pos.mpr (mixedPowerDerivative_det_ne_zero k hk x (rootBox_isUnit hρ hx))

/-- A positive Jacobian lower bound gives the reverse measure estimate on
an injective chart. -/
theorem power_chart_map_le_volume (k : ℕ) {m : ℝ} (hm : 0 < m)
    {U : Set (mixedSpace K)} (hU : MeasurableSet U)
    (hdet : ∀ x ∈ U, m ≤ |(mixedPowerDerivative k x).det|)
    (hinj : Set.InjOn (fun x : mixedSpace K => x ^ k) U) :
    Measure.map (fun x : mixedSpace K => x ^ k) (volume.restrict U) ≤
      (ENNReal.ofReal m)⁻¹ • volume := by
  let f : mixedSpace K → mixedSpace K := fun x => x ^ k
  let J : mixedSpace K → ENNReal := fun x => ENNReal.ofReal |(mixedPowerDerivative k x).det|
  have hf : Measurable f := (continuous_id.pow k).measurable
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar volume hU.nullMeasurableSet
    (fun x _ => (hasFDerivAt_pow (𝕜 := ℝ) (x := x) k).hasFDerivWithinAt) hinj
  change Measure.map f ((volume.restrict U).withDensity J) = volume.restrict (f '' U) at hJac
  have hden : ENNReal.ofReal m • volume.restrict U ≤ (volume.restrict U).withDensity J := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hU] with x hx
    exact ENNReal.ofReal_le_ofReal (hdet x hx)
  have hmap := Measure.map_mono hden hf
  rw [Measure.map_smul, hJac] at hmap
  have hs := measure_smul_mono ((ENNReal.ofReal m)⁻¹) (hmap.trans Measure.restrict_le_self)
  simpa only [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hm).ne'
    ENNReal.ofReal_ne_top, one_smul] using hs

/-- A finite injective-chart cover gives an unconditional finite global
upper density constant for the actual power-image of the fixed root box. -/
theorem exists_rootBox_power_map_upper (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    ∃ C : ENNReal, C < ⊤ ∧
      Measure.map (fun x : mixedSpace K => x ^ k) (volume.restrict (rootBox K ρ R)) ≤ C • volume := by
  obtain ⟨m, hm, hdet⟩ := exists_rootBox_jacobian_lower (K := K) k hk ρ R hρ
  let D := rootBox K ρ R
  have hD : MeasurableSet D := (rootBox_isCompact (K := K) ρ R).measurableSet
  have hcharts (x : D) : ∃ U : Set (mixedSpace K), IsOpen U ∧ (x : mixedSpace K) ∈ U ∧
      Set.InjOn (fun z : mixedSpace K => z ^ k) U := by
    obtain ⟨U, hU, hx, -, hinj⟩ := exists_injective_mixed_power_chart (K := K)
      k hk (x : mixedSpace K) 0 (rootBox_isUnit (K := K) hρ x.property) 1 zero_lt_one
    exact ⟨U, hU, hx, by simpa only [add_zero] using hinj⟩
  choose U hU hxU hinj using hcharts
  obtain ⟨T, hT⟩ := (rootBox_isCompact (K := K) ρ R).elim_finite_subcover U hU (by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hf : Measurable (fun x : mixedSpace K => x ^ k) := (continuous_id.pow k).measurable
  have hloc (j : D) : Measure.map (fun x : mixedSpace K => x ^ k)
      (volume.restrict (D ∩ U j)) ≤ (ENNReal.ofReal m)⁻¹ • volume :=
    power_chart_map_le_volume k hm (hD.inter (hU j).measurableSet)
      (fun x hx => hdet x hx.1) ((hinj j).mono Set.inter_subset_right)
  refine ⟨(T.card : ENNReal) * (ENNReal.ofReal m)⁻¹,
    ENNReal.mul_lt_top (by simp) (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hm)), ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA)]
  have hcover : (fun x : mixedSpace K => x ^ k) ⁻¹' A ∩ D ⊆
      ⋃ j ∈ T, (fun x : mixedSpace K => x ^ k) ⁻¹' A ∩ (D ∩ U j) := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hT hx.2)
    exact Set.mem_iUnion₂.mpr ⟨j, hj, hx.1, hx.2, hxj⟩
  calc
    _ ≤ volume (⋃ j ∈ T, (fun x : mixedSpace K => x ^ k) ⁻¹' A ∩ (D ∩ U j)) := measure_mono hcover
    _ ≤ ∑ j ∈ T, volume ((fun x : mixedSpace K => x ^ k) ⁻¹' A ∩ (D ∩ U j)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ T, (ENNReal.ofReal m)⁻¹ * volume A := by
      apply Finset.sum_le_sum
      intro j hj
      have h := Measure.le_iff.mp (hloc j) A hA
      simpa only [Measure.map_apply hf hA, Measure.restrict_apply (hf hA),
        Measure.smul_apply, smul_eq_mul] using h
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Measure.smul_apply, smul_eq_mul, mul_assoc]

/-- The upper constant is uniform in every translation. -/
theorem exists_rootBox_shifted_power_map_upper (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ c : mixedSpace K,
      Measure.map (fun x : mixedSpace K => x ^ k + c)
        (volume.restrict (rootBox K ρ R)) ≤ C • volume := by
  obtain ⟨C, hC, hbound⟩ := exists_rootBox_power_map_upper (K := K) k hk ρ R hρ
  refine ⟨C, hC, ?_⟩
  intro c
  have hpow : Measurable (fun x : mixedSpace K => x ^ k) := (continuous_id.pow k).measurable
  have hadd : Measurable (fun x : mixedSpace K => x + c) :=
    (continuous_id.add continuous_const).measurable
  have h := Measure.map_mono hbound hadd
  rw [Measure.map_map hadd hpow, Measure.map_smul,
    Measure.IsAddRightInvariant.map_add_right_eq_self] at h
  exact h

/-- The actual full Waring pushforward is bounded above by a finite
multiple of Lebesgue measure. -/
theorem exists_archimedeanWaringMeasure_upper (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    ∃ C : ENNReal, C < ⊤ ∧ archimedeanWaringMeasure (K := K) k s ρ R ≤ C • volume := by
  obtain ⟨C, hC, hbound⟩ := exists_rootBox_shifted_power_map_upper (K := K) k hk ρ R hρ
  letI : BorelSpace (ArchimedeanTupleSpace K s) := inferInstance
  letI : SigmaFinite (volume : Measure (Fin s → mixedSpace K)) := by
    change SigmaFinite (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.sigmaFinite _
  letI : IsFiniteMeasureOnCompacts (volume : Measure (Fin s → mixedSpace K)) := by
    change IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.isFiniteMeasureOnCompacts _
  have hf : Measurable (archimedeanWaringMap (K := K) k s) := by
    apply Continuous.measurable
    unfold archimedeanWaringMap
    fun_prop
  let D := rootBox K ρ R
  let T : Set (Fin s → mixedSpace K) := {y | ∀ i, y i ∈ D}
  have hTc : IsCompact T := isCompact_pi_infinite fun _ => rootBox_isCompact (K := K) ρ R
  refine ⟨C * volume T, ENNReal.mul_lt_top hC hTc.measure_lt_top, ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  unfold archimedeanWaringMeasure
  rw [Measure.map_apply hf hA]
  change ((volume.prod volume).restrict (D ×ˢ T)) ((archimedeanWaringMap k s) ⁻¹' A) ≤ _
  rw [← Measure.prod_restrict, Measure.prod_apply_symm (hf hA)]
  have hy (y : Fin s → mixedSpace K) :
      (volume.restrict D) {x | archimedeanWaringMap k s (x, y) ∈ A} ≤ C * volume A := by
    have h := Measure.le_iff.mp (hbound (∑ i, (y i) ^ k)) A hA
    have hymeas : Measurable (fun x : mixedSpace K => x ^ k + ∑ i, (y i) ^ k) := by fun_prop
    simpa only [Measure.map_apply hymeas hA, Measure.smul_apply, smul_eq_mul] using h
  calc
    _ ≤ ∫⁻ _y : Fin s → mixedSpace K, C * volume A ∂volume.restrict T :=
      lintegral_mono hy
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ,
      Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

/-- A genuine global essential bound for the Radon–Nikodym density. -/
theorem exists_archimedeanWaringDensity_upper (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂(volume : Measure (mixedSpace K)),
      (archimedeanWaringDensity k s ρ R x).toReal ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_archimedeanWaringMeasure_upper (K := K) k s hk ρ R hρ
  have hden : archimedeanWaringDensity (K := K) k s ρ R ≤ᵐ[volume] fun _ => C := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (archimedeanWaringDensity_measurable k s ρ R)
    intro A hA _
    rw [← withDensity_apply _ hA, archimedeanWaringDensity_measure k s hk ρ R hρ]
    have h := Measure.le_iff.mp hbound A hA
    simpa only [lintegral_const, Measure.restrict_apply_univ,
      Measure.smul_apply, smul_eq_mul] using h
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [hden] with x hx
  exact ENNReal.toReal_mono hC.ne hx

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_archimedeanWaringMeasure_upper
#print axioms WaringSiegel.WSL2.exists_archimedeanWaringDensity_upper
