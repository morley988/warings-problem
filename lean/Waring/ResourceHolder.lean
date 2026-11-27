import Waring.Holder
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Analytic meaning of resource weights and unused capacity

The functions are normalized to lie in [0,1]. Factor loads at most one
allow the unused part of each factor to be bounded trivially. Hölder mass
at most one is completed by the constant function one. Repeated resources
for the same factor are allowed and are grouped exactly by their factor.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Waring.ResourceHolder

theorem rpow_sum_nonneg {ι : Type*} (s : Finset ι) (x : ℝ≥0∞)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    x ^ (∑ i ∈ s, w i) = ∏ i ∈ s, x ^ w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        ENNReal.rpow_add_of_nonneg _ _ (hw i (by simp))
          (Finset.sum_nonneg (fun j hj => hw j (by simp [hj])))]
      rw [ih (fun j hj => hw j (by simp [hj]))]

/-- General finite Hölder with an explicit unused-mass factor. -/
theorem holder_with_unused_mass {α ρ : Type*} [MeasurableSpace α] [Fintype ρ]
    {μ : Measure α} (f : ρ → α → ℝ≥0∞) (w : ρ → ℝ)
    (hf : ∀ r, AEMeasurable (f r) μ) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1) :
    (∫⁻ x, ∏ r, f r x ^ w r ∂μ) ≤
      (μ Set.univ) ^ (1 - ∑ r, w r) * ∏ r, (∫⁻ x, f r x ∂μ) ^ w r := by
  classical
  let F : Option ρ → α → ℝ≥0∞ := fun r => r.elim (fun _ => 1) f
  let W : Option ρ → ℝ := fun r => r.elim (1-∑ r, w r) w
  have hF : ∀ r ∈ (Finset.univ : Finset (Option ρ)), AEMeasurable (F r) μ := by
    intro r hr
    cases r with
    | none => exact aemeasurable_const
    | some r => exact hf r
  have hW : ∀ r ∈ (Finset.univ : Finset (Option ρ)), 0 ≤ W r := by
    intro r hr
    cases r with
    | none => exact sub_nonneg.mpr hmass
    | some r => exact hw r
  have hsum : ∑ r : Option ρ, W r = 1 := by
    simp [Fintype.sum_option, W]
  have hh := ENNReal.lintegral_prod_norm_pow_le Finset.univ hF hsum hW
  simpa [Fintype.prod_option, F, W] using hh

/-- Pointwise regrouping by factor. This is where the factor-load condition
enters; no moment estimate or integral inequality is hidden in the premise. -/
theorem product_le_resources {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
    (x : ι → ℝ≥0∞) (factor : ρ → ι) (p w : ρ → ℝ)
    (hx : ∀ i, x i ≤ 1) (hp : ∀ r, 0 ≤ p r) (hw : ∀ r, 0 ≤ w r)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r = i), p r*w r ≤ 1) :
    (∏ i, x i) ≤ ∏ r, (x (factor r)^p r)^w r := by
  classical
  calc
    (∏ i, x i) ≤ ∏ i, (x i) ^ (∑ r ∈ Finset.univ.filter (fun r => factor r = i), p r*w r) := by
      apply Finset.prod_le_prod'
      intro i hi
      simpa only [ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow_of_exponent_ge (hx i) (hload i)
    _ = ∏ i, ∏ r ∈ Finset.univ.filter (fun r => factor r = i), (x (factor r)^p r)^w r := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [rpow_sum_nonneg _ _ _ (fun r hr => mul_nonneg (hp r) (hw r))]
      apply Finset.prod_congr rfl
      intro r hr
      rw [(Finset.mem_filter.mp hr).2, ← ENNReal.rpow_mul]
    _ = _ := Finset.prod_fiberwise Finset.univ factor (fun r => (x (factor r)^p r)^w r)

/-- Actual integral resource allocation, with both unused mass and unused
factor loads. In applications the normalized factors are the quadratic sum
and coefficient sums, and each resource supplies one moment on the right. -/
theorem integral_resource_allocation {α ι ρ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype ρ] [DecidableEq ι] {μ : Measure α}
    (f : ι → α → ℝ≥0∞) (factor : ρ → ι) (p w : ρ → ℝ)
    (hf : ∀ i, AEMeasurable (f i) μ) (hcap : ∀ i x, f i x ≤ 1)
    (hp : ∀ r, 0 ≤ p r) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r = i), p r*w r ≤ 1) :
    (∫⁻ x, ∏ i, f i x ∂μ) ≤
      (μ Set.univ) ^ (1 - ∑ r, w r) *
        ∏ r, (∫⁻ x, f (factor r) x ^ p r ∂μ) ^ w r := by
  apply (lintegral_mono (fun x => product_le_resources (fun i => f i x)
    factor p w (fun i => hcap i x) hp hw hload)).trans
  exact holder_with_unused_mass (fun r x => f (factor r) x ^ p r) w
    (fun r => (hf (factor r)).pow_const _) hw hmass

/-- On a probability space the unused Hölder mass has no cost. -/
theorem probability_resource_allocation {α ι ρ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype ρ] [DecidableEq ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ι → α → ℝ≥0∞) (factor : ρ → ι) (p w : ρ → ℝ)
    (hf : ∀ i, AEMeasurable (f i) μ) (hcap : ∀ i x, f i x ≤ 1)
    (hp : ∀ r, 0 ≤ p r) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r = i), p r*w r ≤ 1) :
    (∫⁻ x, ∏ i, f i x ∂μ) ≤ ∏ r, (∫⁻ x, f (factor r) x ^ p r ∂μ) ^ w r := by
  simpa using integral_resource_allocation f factor p w hf hcap hp hw hmass hload

theorem rpow_sum_finite {ι : Type*} (s : Finset ι) (P : ℝ≥0∞)
    (hP0 : P ≠ 0) (hPtop : P ≠ ⊤) (b : ι → ℝ) :
    P^(∑ i ∈ s, b i) = ∏ i ∈ s, P^b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        ENNReal.rpow_add _ _ hP0 hPtop, ih]

/-- The resource savings add with exactly the certificate weights. No
positivity is imposed on a saving: a moment loss is permitted as well. -/
theorem product_resource_bounds {ρ : Type*} [Fintype ρ]
    (P : ℝ≥0∞) (hP0 : P ≠ 0) (hPtop : P ≠ ⊤)
    (C : ρ → ℝ≥0∞) (b w : ρ → ℝ) (hw : ∀ r, 0 ≤ w r) :
    (∏ r, (C r * P^(-b r))^w r) =
      (∏ r, C r^w r) * P^(-(∑ r, w r*b r)) := by
  classical
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (hw _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← ENNReal.rpow_mul]
  rw [← rpow_sum_finite _ _ hP0 hPtop]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem probability_resource_saving {α ι ρ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype ρ] [DecidableEq ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ι → α → ℝ≥0∞) (factor : ρ → ι) (p w : ρ → ℝ)
    (hf : ∀ i, AEMeasurable (f i) μ) (hcap : ∀ i x, f i x ≤ 1)
    (hp : ∀ r, 0 ≤ p r) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r = i), p r*w r ≤ 1)
    (P : ℝ≥0∞) (hP0 : P ≠ 0) (hPtop : P ≠ ⊤)
    (C : ρ → ℝ≥0∞) (b : ρ → ℝ)
    (hresources : ∀ r, (∫⁻ x, f (factor r) x^p r ∂μ) ≤ C r*P^(-b r)) :
    (∫⁻ x, ∏ i, f i x ∂μ) ≤
      (∏ r, C r^w r) * P^(-(∑ r, w r*b r)) := by
  apply (probability_resource_allocation f factor p w hf hcap hp hw hmass hload).trans
  rw [← product_resource_bounds P hP0 hPtop C b w hw]
  exact Finset.prod_le_prod' (fun r hr => ENNReal.rpow_le_rpow (hresources r) (hw r))

#print axioms integral_resource_allocation
#print axioms probability_resource_allocation
#print axioms probability_resource_saving

end Waring.ResourceHolder
