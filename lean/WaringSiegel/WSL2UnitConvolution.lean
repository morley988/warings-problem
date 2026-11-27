import WaringSiegel.WSL2UnitMeasure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual archimedean convolution volume near every positive target

The pushforward below varies every root coordinate. An augmented Waring map
retains the free coordinates, so the ordinary equal-dimensional Jacobian
formula applies. Projecting a genuine product neighborhood supplies positive
Lebesgue domination for the full sum-of-powers pushforward measure.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

abbrev ArchimedeanTupleSpace (K : Type*) [Field K] (s : ℕ) :=
  mixedSpace K × (Fin s → mixedSpace K)

def rootTupleBox (s : ℕ) (ρ R : ℝ) : Set (ArchimedeanTupleSpace K s) :=
  rootBox K ρ R ×ˢ {y | ∀ i, y i ∈ rootBox K ρ R}

theorem rootTupleBox_isCompact (s : ℕ) (ρ R : ℝ) :
    IsCompact (rootTupleBox (K := K) s ρ R) :=
  (rootBox_isCompact ρ R).prod (isCompact_pi_infinite fun _ => rootBox_isCompact ρ R)

def archimedeanWaringMap (k s : ℕ) (x : ArchimedeanTupleSpace K s) : mixedSpace K :=
  x.1 ^ k + ∑ i, (x.2 i) ^ k

def augmentedWaringMap (k s : ℕ) (x : ArchimedeanTupleSpace K s) : ArchimedeanTupleSpace K s :=
  (archimedeanWaringMap k s x, x.2)

theorem contDiff_augmentedWaringMap (k s : ℕ) :
    ContDiff ℝ 1 (augmentedWaringMap (K := K) k s) := by
  unfold augmentedWaringMap archimedeanWaringMap
  fun_prop

def archimedeanWaringMeasure (k s : ℕ) (ρ R : ℝ) : Measure (mixedSpace K) :=
  Measure.map (archimedeanWaringMap k s) (volume.restrict (rootTupleBox s ρ R))

/-- The Jacobian bound is uniform over every tuple in the fixed compact box. -/
theorem exists_augmented_jacobian_bound (k s : ℕ) (ρ R : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ rootTupleBox (K := K) s ρ R,
      |(fderiv ℝ (augmentedWaringMap k s) x).det| ≤ M := by
  have hc : Continuous (fun x : ArchimedeanTupleSpace K s =>
      |(fderiv ℝ (augmentedWaringMap k s) x).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      ((contDiff_augmentedWaringMap k s).continuous_fderiv le_rfl)).abs
  obtain ⟨M, hM, hb⟩ := ((rootTupleBox_isCompact (K := K) s ρ R).image hc).isBounded.exists_pos_norm_le
  refine ⟨M, hM, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_abs] using hb _ (Set.mem_image_of_mem _ hx)

theorem augmentedWaringMap_injOn (k s : ℕ) {U : Set (mixedSpace K)}
    (hU : Set.InjOn (fun x : mixedSpace K => x ^ k) U) (W : Set (Fin s → mixedSpace K)) :
    Set.InjOn (augmentedWaringMap k s) (U ×ˢ W) := by
  intro p hp q hq he
  have htail := congrArg (fun z : ArchimedeanTupleSpace K s => z.2) he
  change p.2 = q.2 at htail
  have hsum : p.1 ^ k + ∑ i, (p.2 i) ^ k = q.1 ^ k + ∑ i, (q.2 i) ^ k := congrArg Prod.fst he
  rw [htail] at hsum
  exact Prod.ext (hU hp.1 hq.1 (add_right_cancel hsum)) htail

/-- An actual injective augmented chart, whose image contains an open
neighborhood in both target and free-coordinate directions. -/
theorem exists_augmented_waring_chart (k s : ℕ) (hk : 0 < k)
    {ρ R : ℝ} (hρ : 0 < ρ) (a : mixedSpace K) (ha : IsUnit a)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall a r ⊆ rootBox K ρ R) :
    ∃ U O : Set (ArchimedeanTupleSpace K s), IsOpen U ∧ IsOpen O ∧
      U ⊆ rootTupleBox s ρ R ∧ Set.InjOn (augmentedWaringMap k s) U ∧
      augmentedWaringMap k s (a, fun _ => a) ∈ O ∧ O ⊆ augmentedWaringMap k s '' U := by
  obtain ⟨V, hV, haV, hVr, hVinj⟩ := exists_injective_mixed_power_chart k hk a 0 ha r hr
  have hVbox : V ⊆ rootBox K ρ R := hVr.trans (Metric.ball_subset_closedBall.trans hball)
  have hinj : Set.InjOn (fun x : mixedSpace K => x ^ k) V := by
    simpa only [add_zero] using hVinj
  let W : Set (Fin s → mixedSpace K) := Metric.ball (fun _ => a) r
  have hWbox : W ⊆ {y | ∀ i, y i ∈ rootBox K ρ R} := by
    intro y hy i
    apply hball
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    have hi := norm_le_pi_norm (y - fun _ => a) i
    have hy' : ‖y - (fun _ => a)‖ < r := by
      simpa only [W, Metric.mem_ball, dist_eq_norm] using hy
    exact hi.trans hy'.le
  have himage : IsOpen ((fun x : mixedSpace K => x ^ k) '' V) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← mixed_pow_map_nhds k hk x (rootBox_isUnit hρ (hVbox hx))]
    exact Filter.image_mem_map (hV.mem_nhds hx)
  let O : Set (ArchimedeanTupleSpace K s) :=
    {z | z.2 ∈ W ∧ z.1 - ∑ i, (z.2 i)^k ∈ (fun x : mixedSpace K => x^k) '' V}
  have hO : IsOpen O := by
    apply (Metric.isOpen_ball.preimage continuous_snd).inter
    exact himage.preimage (by fun_prop)
  refine ⟨V ×ˢ W, O, hV.prod Metric.isOpen_ball, hO,
    fun x hx => ⟨hVbox hx.1, hWbox hx.2⟩, augmentedWaringMap_injOn k s hinj W, ?_, ?_⟩
  · constructor
    · exact Metric.mem_ball_self hr
    · change (a ^ k + ∑ i : Fin s, a ^ k) - ∑ i : Fin s, a ^ k ∈ _
      rw [add_sub_cancel_right]
      exact ⟨a, haV, rfl⟩
  · intro z hz
    obtain ⟨x, hx, hxeq⟩ := hz.2
    refine ⟨(x, z.2), ⟨hx, hz.1⟩, ?_⟩
    apply Prod.ext
    · change x ^ k + ∑ i, (z.2 i)^k = z.1
      change x ^ k = z.1 - ∑ i, (z.2 i)^k at hxeq
      rw [hxeq, sub_add_cancel]
    · rfl

/-- The actual full sum-of-powers measure dominates a positive multiple of
Lebesgue measure on a neighborhood of each nonsingular equal-root target.
All free root coordinates vary over sets of positive volume. -/
theorem archimedeanWaringMeasure_local_lower_bound (k s : ℕ) (hk : 0 < k)
    {ρ R : ℝ} (hρ : 0 < ρ) (a : mixedSpace K) (ha : IsUnit a)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall a r ⊆ rootBox K ρ R) :
    ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ ∃ ε : ℝ, 0 < ε ∧
      c • volume.restrict (Metric.ball (archimedeanWaringMap k s (a, fun _ => a)) ε) ≤
        archimedeanWaringMeasure k s ρ R := by
  obtain ⟨M, hM, hMb⟩ := exists_augmented_jacobian_bound (K := K) k s ρ R
  obtain ⟨U, O, hU, hO, hUbox, hinj, hanchor, hOimage⟩ :=
    exists_augmented_waring_chart k s hk hρ a ha r hr hball
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hanchor)
  let b := archimedeanWaringMap k s (a, fun _ => a)
  let V := Metric.ball b ε
  let W : Set (Fin s → mixedSpace K) := Metric.ball (fun _ => a) ε
  have hVW : V ×ˢ W ⊆ augmentedWaringMap k s '' U := by
    rw [ball_prod_same]
    exact hεO.trans hOimage
  have hder : Differentiable ℝ (augmentedWaringMap (K := K) k s) :=
    (contDiff_augmentedWaringMap k s).differentiable le_rfl
  letI : BorelSpace (ArchimedeanTupleSpace K s) := inferInstance
  letI : SigmaFinite (volume : Measure (Fin s → mixedSpace K)) := by
    change SigmaFinite (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.sigmaFinite _
  letI : IsFiniteMeasureOnCompacts (volume : Measure (Fin s → mixedSpace K)) := by
    change IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.isFiniteMeasureOnCompacts _
  letI : MeasurableAdd₂ (mixedSpace K) := ⟨continuous_add.measurable⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure (Fin s → mixedSpace K)) := by
    change Measure.IsAddHaarMeasure (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.isAddHaarMeasure _
  letI : Measure.IsAddHaarMeasure (volume : Measure (ArchimedeanTupleSpace K s)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hdom := measure_domination_of_jacobian_bound
    (volume : Measure (ArchimedeanTupleSpace K s))
    (augmentedWaringMap (K := K) k s) (fderiv ℝ (augmentedWaringMap k s))
    (contDiff_augmentedWaringMap k s).continuous.measurable
    (rootTupleBox s ρ R) M hMb hU.measurableSet hUbox
    (fun x _ => (hder x).hasFDerivAt.hasFDerivWithinAt) hinj
  have hprod : volume.restrict (V ×ˢ W) ≤ ENNReal.ofReal M •
      Measure.map (augmentedWaringMap k s) (volume.restrict (rootTupleBox s ρ R)) :=
    (Measure.restrict_mono hVW le_rfl).trans hdom
  have hproj := Measure.map_mono hprod measurable_fst
  rw [Measure.map_smul, Measure.map_map measurable_fst
    (contDiff_augmentedWaringMap k s).continuous.measurable] at hproj
  change Measure.map Prod.fst ((volume.prod volume).restrict (V ×ˢ W)) ≤
    ENNReal.ofReal M • archimedeanWaringMeasure k s ρ R at hproj
  rw [← Measure.prod_restrict, Measure.map_fst_prod, Measure.restrict_apply_univ] at hproj
  have hWpos : 0 < (volume : Measure (Fin s → mixedSpace K)) W := Metric.measure_ball_pos volume _ hε
  have hWfin : (volume : Measure (Fin s → mixedSpace K)) W < ⊤ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall) (isCompact_closedBall _ _).measure_lt_top
  have hMpos : 0 < ENNReal.ofReal M := ENNReal.ofReal_pos.mpr hM
  let c : ENNReal := (ENNReal.ofReal M)⁻¹ * volume W
  refine ⟨c, ENNReal.mul_pos (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top).ne' hWpos.ne',
    ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hMpos) hWfin, ε, hε, ?_⟩
  have hscaled := measure_smul_mono ((ENNReal.ofReal M)⁻¹) hproj
  simpa only [smul_smul, ENNReal.inv_mul_cancel hMpos.ne' ENNReal.ofReal_ne_top, one_smul]
    using hscaled

/-- Increasing the scalar increases an actual measure. -/
theorem measure_smul_mono_scalar {X : Type*} [MeasurableSpace X]
    {c d : ENNReal} (h : c ≤ d) (μ : Measure X) : c • μ ≤ d • μ := by
  apply Measure.le_iff.mpr
  intro S hS
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right' h (μ S)

/-- Compactness turns genuinely positive local domination constants into
one positive constant valid at every point of the compact target set. -/
theorem compact_uniform_local_measure_lower {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E]
    (μ₀ μ : Measure E) {S : Set E} (hS : IsCompact S)
    (hloc : ∀ b ∈ S, ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧
      ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ c • μ₀.restrict V ≤ μ) :
    ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ ∀ b ∈ S,
      ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ c • μ₀.restrict V ≤ μ := by
  by_cases hne : S.Nonempty
  · let c : S → ENNReal := fun b => Classical.choose (hloc b b.property)
    have hc (b : S) : 0 < c b ∧ c b < ⊤ ∧
        ∃ V : Set E, IsOpen V ∧ (b : E) ∈ V ∧ c b • μ₀.restrict V ≤ μ :=
      Classical.choose_spec (hloc b b.property)
    let V : S → Set E := fun b => Classical.choose (hc b).2.2
    have hV (b : S) : IsOpen (V b) ∧ (b : E) ∈ V b ∧ c b • μ₀.restrict (V b) ≤ μ :=
      Classical.choose_spec (hc b).2.2
    obtain ⟨T, hT⟩ := hS.elim_finite_subcover V (fun b => (hV b).1) (by
      intro b hb
      exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, (hV ⟨b, hb⟩).2.1⟩)
    obtain ⟨b₀, hb₀⟩ := hne
    obtain ⟨j₀, hj₀, _⟩ := Set.mem_iUnion₂.mp (hT hb₀)
    have hTne : T.Nonempty := ⟨j₀, hj₀⟩
    refine ⟨T.inf' hTne c, (Finset.lt_inf'_iff _).mpr (fun j _ => (hc j).1),
      (Finset.inf'_le c hj₀).trans_lt (hc j₀).2.1, ?_⟩
    intro b hb
    obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.mp (hT hb)
    exact ⟨V j, (hV j).1, hbj,
      (measure_smul_mono_scalar (Finset.inf'_le c hj) _).trans (hV j).2.2⟩
  · exact ⟨1, zero_lt_one, ENNReal.one_lt_top, fun b hb => False.elim (hne ⟨b, hb⟩)⟩

/-- A fixed compact positive root box and one strictly positive constant
give local Lebesgue domination for the actual full `(s+1)`-variable
sum-of-powers pushforward, uniformly over all normalized targets.

This is a volume statement for the genuine convolution measure. No Fourier
inversion or unproved singular-integral identity is assumed. -/
theorem exists_uniform_archimedean_volume_lower (k s : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ IsCompact (rootBox K ρ R) ∧
      ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧
        ∀ b ∈ compactTargetSet K B, ∃ V : Set (mixedSpace K),
          IsOpen V ∧ b ∈ V ∧ c • volume.restrict V ≤ archimedeanWaringMeasure k s ρ R := by
  obtain ⟨ρ₀, R₀, hρ₀, hR₀, hanchors⟩ :=
    exists_uniform_anchor_bounds (K := K) k (s + 1) hk (by omega) B hB
  refine ⟨ρ₀ / 2, R₀ + ρ₀ / 2, by positivity, by positivity, rootBox_isCompact _ _, ?_⟩
  apply compact_uniform_local_measure_lower volume _ (compactTargetSet_isCompact B)
  intro b hb
  obtain ⟨a, hsum, hap, hau, hab⟩ := hanchors b hb
  have he : archimedeanWaringMap k s (a, fun _ => a) = b := by
    simpa only [archimedeanWaringMap, Fin.sum_univ_succ] using hsum
  obtain ⟨c, hc, hcfin, ε, hε, hdom⟩ := archimedeanWaringMeasure_local_lower_bound
    k s hk (by positivity : 0 < ρ₀ / 2) a hau (ρ₀ / 2) (by positivity)
    (closedBall_anchor_subset_rootBox hρ₀ hap hab)
  rw [he] at hdom
  exact ⟨c, hc, hcfin, Metric.ball b ε, Metric.isOpen_ball, Metric.mem_ball_self hε, hdom⟩

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.archimedeanWaringMeasure_local_lower_bound
#print axioms WaringSiegel.WSL2.exists_uniform_archimedean_volume_lower
