import Waring.ProductBoxIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! # Product-box integrals as actual probability integrals -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox

def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  simp [unitIntervalMeasure,Real.volume_Icc]

def boxMeasure (L : ℕ) : Measure (Fin L → ℝ) := Measure.pi (fun _ => unitIntervalMeasure)

instance (L : ℕ) : IsProbabilityMeasure (boxMeasure L) := by
  unfold boxMeasure
  infer_instance

theorem integrable_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x,‖f x‖≤B) : Integrable f μ :=
  (integrable_const B).mono' hf (Filter.Eventually.of_forall hB)

theorem integral_boxMeasure_eq (L : ℕ) (f : (Fin L → ℝ) → ℂ) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x,‖f x‖≤B) :
    (∫ x,f x ∂boxMeasure L)=boxIntegral L 1 f := by
  induction L with
  | zero =>
    rw [integral_unique]
    simp only [measureReal_univ_eq_one,one_smul,boxIntegral_zero]
    congr 1
  | succ L ih =>
    let μ := fun _i : Fin (L+1) => unitIntervalMeasure
    have hpres := (measurePreserving_piFinSuccAbove μ 0).symm
    have he : (∫ x,f x ∂boxMeasure (L+1))=
        ∫ z : ℝ×(Fin L → ℝ),f (Fin.cons z.1 z.2) ∂unitIntervalMeasure.prod (boxMeasure L) := by
      unfold boxMeasure
      rw [← hpres.integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Fin.insertNth_zero,Equiv.coe_fn_mk,Fin.zero_succAbove,cast_eq]
      rfl
    rw [he]
    have hi : Integrable (fun z : ℝ×(Fin L → ℝ) => f (Fin.cons z.1 z.2))
        (unitIntervalMeasure.prod (boxMeasure L)) :=
      integrable_bounded (hf.comp (continuous_cons continuous_fst continuous_snd)).aestronglyMeasurable
        (fun z => hB _)
    rw [integral_prod _ hi]
    rw [boxIntegral_succ]
    apply integral_congr_ae
    filter_upwards with t
    exact ih (fun y => f (Fin.cons t y)) (hf.comp (continuous_cons continuous_const continuous_id))
      (fun y => hB _)

#print axioms integral_boxMeasure_eq
end Waring.ProductBox
