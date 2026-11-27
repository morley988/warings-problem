import WaringSiegel.WSL2MomentFourier
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Literal finite differencing on arbitrary additive lattices

The exact autocorrelation identity and Cauchy inequality below work directly
in the additive group of algebraic integers.  They retain the nonnegative
aggregate required by Hua's moment argument.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

variable {G : Type*} [AddCommGroup G]

def additiveDifferences (S : Finset G) : Finset G :=
  (S.product S).image (fun p => p.1 - p.2)

def additiveOverlap (S : Finset G) (h : G) : Finset G :=
  S.filter (fun x => x + h ∈ S)

omit [AddCommGroup G] in
theorem finite_sum_norm_sq_pair_expansion (S : Finset G) (f : G → ℂ) :
    ((‖∑ x ∈ S, f x‖^2 : ℝ) : ℂ) =
      ∑ p ∈ S.product S, f p.1 * conj (f p.2) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  exact (Finset.sum_product S S (fun p => f p.1 * conj (f p.2))).symm

theorem additive_difference_fiber_sum (S : Finset G) (f : G → ℂ) (h : G) :
    (∑ p ∈ (S.product S).filter (fun p => p.1 - p.2 = h),
      f p.1 * conj (f p.2)) =
      ∑ x ∈ additiveOverlap S h, f (x + h) * conj (f x) := by
  apply Finset.sum_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hmem, hdiff⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hmem
    refine Finset.mem_filter.mpr ⟨hp2, ?_⟩
    have heq : p.2 + h = p.1 := by rw [← hdiff]; abel
    rwa [heq]
  · intro p hp q hq heq
    apply Prod.ext
    · have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      have : p.1 - p.2 = q.1 - p.2 := by rw [hp', heq, hq']
      exact sub_left_injective this
    · exact heq
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    refine ⟨(x + h, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxh, hx⟩, ?_⟩, rfl⟩
    simp only [add_sub_cancel_left]
  · intro p hp
    have hdiff := (Finset.mem_filter.mp hp).2
    have heq : p.2 + h = p.1 := by rw [← hdiff]; abel
    rw [heq]

/-- Exact autocorrelation with any finite container for all relevant shifts. -/
theorem finite_sum_norm_sq_autocorrelations (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (f : G → ℂ) :
    ((‖∑ x ∈ S, f x‖^2 : ℝ) : ℂ) =
      ∑ h ∈ H, ∑ x ∈ additiveOverlap S h, f (x + h) * conj (f x) := by
  rw [finite_sum_norm_sq_pair_expansion]
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S.product S) (t := H) (g := fun p => p.1 - p.2)
    (fun p hp => hH p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
    (fun p => f p.1 * conj (f p.2))
  rw [← hfiber]
  exact Finset.sum_congr rfl (fun h _ => additive_difference_fiber_sum S f h)

/-- One genuine Cauchy step; the right hand side is a nonnegative aggregate. -/
theorem finite_sum_fourth_le_correlations (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (f : G → ℂ) :
    ‖∑ x ∈ S, f x‖^4 ≤
      (H.card : ℝ) * ∑ h ∈ H, ‖∑ x ∈ additiveOverlap S h,
        f (x + h) * conj (f x)‖^2 := by
  let g : G → ℂ := fun h => ∑ x ∈ additiveOverlap S h, f (x+h) * conj (f x)
  have heq : ‖∑ x ∈ S, f x‖^4 = ‖∑ h ∈ H, g h‖^2 := by
    rw [← finite_sum_norm_sq_autocorrelations S H hH f]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖∑ x ∈ S, f x‖))]
    ring
  rw [heq]
  have htriangle := norm_sum_le H g
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq H (fun _ => (1 : ℝ)) (fun h => ‖g h‖)
  exact hsquare.trans (by simpa [g] using hcauchy)

theorem additiveOverlap_subset (S : Finset G) (h : G) : additiveOverlap S h ⊆ S :=
  Finset.filter_subset _ _

theorem additiveDifferences_mem (S : Finset G) {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    x - y ∈ additiveDifferences S :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

end WaringSiegel.WSL2
