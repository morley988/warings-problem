import Waring.EndgameCompletionMajor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Iterated integration over a product box

These are literal real integrals. Continuity and the elementary uniform
norm estimate support the product-weight major-arc approximation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox

theorem continuous_cons {X : Type*} [TopologicalSpace X] {L : ℕ}
    {a : X → ℝ} {y : X → Fin L → ℝ} (ha : Continuous a) (hy : Continuous y) :
    Continuous (fun x => (Fin.cons (a x) (y x) : Fin (L+1) → ℝ)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ha
  · exact (continuous_apply j).comp hy

/-- An iterated Lebesgue integral over `[0,M]^L`. -/
def boxIntegral : (L : ℕ) → ℝ → ((Fin L → ℝ) → ℂ) → ℂ
  | 0,_,f => f Fin.elim0
  | L+1,M,f => ∫ t in Set.Icc 0 M,boxIntegral L M (fun y => f (Fin.cons t y))

@[simp] theorem boxIntegral_zero (M : ℝ) (f : (Fin 0 → ℝ) → ℂ) :
    boxIntegral 0 M f=f Fin.elim0 := rfl
@[simp] theorem boxIntegral_succ (L : ℕ) (M : ℝ) (f : (Fin (L+1) → ℝ) → ℂ) :
    boxIntegral (L+1) M f=∫ t in Set.Icc 0 M,boxIntegral L M (fun y => f (Fin.cons t y)) := rfl

theorem continuous_boxIntegral {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] (L : ℕ) (M : ℝ) (f : X → (Fin L → ℝ) → ℂ)
    (hf : Continuous f.uncurry) : Continuous (fun x => boxIntegral L M (f x)) := by
  induction L generalizing X with
  | zero =>
    exact hf.comp (continuous_id.prodMk continuous_const)
  | succ L ih =>
    have hc : Continuous (fun z : X×ℝ => boxIntegral L M (fun y => f z.1 (Fin.cons z.2 y))) := by
      apply ih
      change Continuous (fun z : (X×ℝ)×(Fin L→ℝ) => f z.1.1 (Fin.cons z.1.2 z.2))
      exact hf.comp (continuous_fst.fst.prodMk (continuous_cons continuous_fst.snd continuous_snd))
    exact continuous_parametric_integral_of_continuous hc isCompact_Icc

theorem boxIntegral_integrable_section {L : ℕ} {M : ℝ}
    {f : (Fin (L+1) → ℝ) → ℂ} (hf : Continuous f) :
    IntegrableOn (fun t => boxIntegral L M (fun y => f (Fin.cons t y))) (Set.Icc 0 M) := by
  have hc : Continuous (fun t => boxIntegral L M (fun y => f (Fin.cons t y))) := by
    apply continuous_boxIntegral
    exact hf.comp (continuous_cons continuous_fst continuous_snd)
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

theorem boxIntegral_congr (L : ℕ) (M : ℝ) {f g : (Fin L → ℝ) → ℂ}
    (h : ∀ x,(∀ i, x i ∈ Set.Icc 0 M) → f x=g x) :
    boxIntegral L M f=boxIntegral L M g := by
  induction L with
  | zero => exact h _ (by intro i; exact Fin.elim0 i)
  | succ L ih =>
    rw [boxIntegral_succ,boxIntegral_succ]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    apply ih
    intro y hy
    apply h
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ht
    · exact hy j

theorem boxIntegral_norm_le (L : ℕ) {M B : ℝ} (hM : 0≤M) (hB : 0≤B)
    {f : (Fin L → ℝ) → ℂ} (hf : ∀ x,(∀ i,x i ∈ Set.Icc 0 M) → ‖f x‖≤B) :
    ‖boxIntegral L M f‖≤B*M^L := by
  induction L with
  | zero => simpa using hf Fin.elim0 (by intro i; exact Fin.elim0 i)
  | succ L ih =>
    rw [boxIntegral_succ]
    have hh := norm_setIntegral_le_of_norm_le_const (s := Set.Icc 0 M) (μ := (volume : Measure ℝ))
      (f := fun t => boxIntegral L M (fun y => f (Fin.cons t y)))
      (C := B*M^L) (measure_Icc_lt_top) (by
        intro t ht
        apply ih
        intro y hy
        apply hf
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ht
        · exact hy j)
    convert hh using 1
    simp only [Real.volume_real_Icc,sub_zero,max_eq_left hM,pow_succ]
    ring

theorem boxIntegral_add (L : ℕ) (M : ℝ) {f g : (Fin L → ℝ) → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    boxIntegral L M (fun x => f x+g x)=boxIntegral L M f+boxIntegral L M g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [boxIntegral_succ]
    have he (t : ℝ) : boxIntegral L M (fun y => f (Fin.cons t y)+g (Fin.cons t y))=
        boxIntegral L M (fun y => f (Fin.cons t y))+boxIntegral L M (fun y => g (Fin.cons t y)) :=
      ih (hf.comp (continuous_cons continuous_const continuous_id))
        (hg.comp (continuous_cons continuous_const continuous_id))
    simp_rw [he]
    exact integral_add (boxIntegral_integrable_section hf) (boxIntegral_integrable_section hg)

theorem boxIntegral_mul_const (L : ℕ) (M : ℝ) (f : (Fin L → ℝ) → ℂ) (c : ℂ) :
    boxIntegral L M (fun x => f x*c)=boxIntegral L M f*c := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [boxIntegral_succ,ih]
    exact integral_mul_const _ _

theorem boxIntegral_const_mul (L : ℕ) (M : ℝ) (f : (Fin L → ℝ) → ℂ) (c : ℂ) :
    boxIntegral L M (fun x => c*f x)=c*boxIntegral L M f := by
  simp_rw [mul_comm c]
  exact boxIntegral_mul_const L M f c

#print axioms boxIntegral_norm_le
#print axioms continuous_boxIntegral
end Waring.ProductBox
