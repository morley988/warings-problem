import WaringSiegel.WSL2UnitDensity

/-!
# Literal sum-of-powers image measures and convolution recursion

The tuple measure is identified with its actual finite product of restricted
Lebesgue measures. Splitting the first coordinate proves the exact recursion
for one additional root.
-/
noncomputable section
open MeasureTheory
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

local instance : BorelSpace (mixedSpace K) := inferInstance

/-- The product box really carries the product of the restricted measures. -/
theorem rootTupleBox_volume (s : ℕ) (ρ R : ℝ) :
    (volume : Measure (ArchimedeanTupleSpace K s)).restrict (rootTupleBox s ρ R) =
      (volume.restrict (rootBox K ρ R)).prod
        (Measure.pi fun _ : Fin s => volume.restrict (rootBox K ρ R)) := by
  letI : SigmaFinite (volume : Measure (Fin s → mixedSpace K)) := by
    change SigmaFinite (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.sigmaFinite _
  let D := rootBox K ρ R
  let T : Set (Fin s → mixedSpace K) := {y | ∀ i, y i ∈ D}
  have hT : T = Set.univ.pi (fun _ : Fin s => D) := by ext y; simp [T]
  have hpi : (volume : Measure (Fin s → mixedSpace K)).restrict T =
      Measure.pi (fun _ : Fin s => volume.restrict D) := by
    rw [hT]
    exact Measure.restrict_pi_pi (fun _ : Fin s => (volume : Measure (mixedSpace K))) (fun _ => D)
  change (volume.prod volume).restrict (D ×ˢ T) = _
  rw [← Measure.prod_restrict, hpi]

/-- The original first-plus-tail definition equals the literal sum on all
s+1 coordinates with the actual product measure. -/
theorem archimedeanWaringMeasure_eq_pi (k s : ℕ) (ρ R : ℝ) :
    archimedeanWaringMeasure (K := K) k s ρ R =
      Measure.map (fun y : Fin (s + 1) → mixedSpace K => ∑ i, (y i)^k)
        (Measure.pi fun _ : Fin (s + 1) => volume.restrict (rootBox K ρ R)) := by
  let μ : Measure (mixedSpace K) := volume.restrict (rootBox K ρ R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (s+1) => μ) 0
  have hmap : Measurable (archimedeanWaringMap (K := K) k s) := by
    apply Continuous.measurable
    unfold archimedeanWaringMap
    fun_prop
  rw [archimedeanWaringMeasure, rootTupleBox_volume]
  change Measure.map (archimedeanWaringMap k s) (μ.prod (Measure.pi fun _ : Fin s => μ)) = _
  rw [← hsplit.map_eq, Measure.map_map hmap hsplit.measurable]
  congr 1
  funext y
  simp [Function.comp_def, archimedeanWaringMap, MeasurableEquiv.piFinSuccAbove,
    Fin.sum_univ_succ, Fin.tail]

/-- One root has exactly the power-map image measure. -/
theorem archimedeanWaringMeasure_zero (k : ℕ) (ρ R : ℝ) :
    archimedeanWaringMeasure (K := K) k 0 ρ R =
      Measure.map (fun x : mixedSpace K => x^k) (volume.restrict (rootBox K ρ R)) := by
  rw [archimedeanWaringMeasure_eq_pi]
  let μ : Measure (mixedSpace K) := volume.restrict (rootBox K ρ R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  have he := measurePreserving_piUnique (fun _ : Fin 1 => μ)
  have hp : Measurable (fun x : mixedSpace K => x^k) := (continuous_id.pow k).measurable
  change Measure.map (fun y : Fin 1 → mixedSpace K => ∑ i, (y i)^k)
    (Measure.pi fun _ : Fin 1 => μ) = Measure.map (fun x : mixedSpace K => x^k) μ
  conv_rhs => rw [← he.map_eq, Measure.map_map hp he.measurable]
  congr 1
  funext y
  simp [Function.comp_def, MeasurableEquiv.piUnique]

/-- Exact convolution recursion for the literal full sum-of-powers measure. -/
theorem archimedeanWaringMeasure_succ (k s : ℕ) (ρ R : ℝ) :
    archimedeanWaringMeasure (K := K) k (s+1) ρ R =
      (archimedeanWaringMeasure k 0 ρ R).conv (archimedeanWaringMeasure k s ρ R) := by
  let μ : Measure (mixedSpace K) := volume.restrict (rootBox K ρ R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  have hp : Measurable (fun x : mixedSpace K => x^k) := (continuous_id.pow k).measurable
  have hs : Measurable (fun y : Fin (s+1) → mixedSpace K => ∑ i, (y i)^k) := by fun_prop
  rw [archimedeanWaringMeasure_zero, archimedeanWaringMeasure_eq_pi k s]
  rw [Measure.conv, Measure.map_prod_map _ _ hp hs, Measure.map_map measurable_add (hp.prodMap hs)]
  rw [archimedeanWaringMeasure, rootTupleBox_volume]
  rfl

end WaringSiegel.WSL2
