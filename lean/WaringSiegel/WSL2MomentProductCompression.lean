import WaringSiegel.WSL2MomentCubicKernel
import WaringSiegel.WSL2MomentDivisorGrowth

/-!
# Compressing the two cubic shifts by their actual product

Nonzero product fibers inject into the actual divisors in the shift box.
The zero product is separated before the epsilon divisor estimate is used.
-/

noncomputable section
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL2
variable {R : Type*} [CommRing R] [IsDomain R]

def shiftProducts (H : Finset R) : Finset R :=
  (H.product H).image (fun p => p.1*p.2)

theorem product_fiber_card_le_divisors (H : Finset R) {a : R} (ha : a ≠ 0) :
    ((H.product H).filter (fun p => p.1*p.2=a)).card ≤
      (H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    obtain ⟨hpmem, hpeq⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hpmem).1, ?_, ⟨p.2, hpeq.symm⟩⟩
    intro hz
    exact ha (by simpa [hz] using hpeq.symm)
  · intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hp0 : p.1 ≠ 0 := by intro hz; exact ha (by simpa [hz] using hp'.symm)
    apply Prod.ext heq
    apply mul_left_cancel₀ hp0
    rw [hp', heq, hq']

theorem product_zero_fiber_card_le (H : Finset R) :
    ((H.product H).filter (fun p => p.1*p.2=0)).card ≤ 2*H.card := by
  have hsub : (H.product H).filter (fun p => p.1*p.2=0) ⊆
      ({0} : Finset R).product H ∪ H.product {0} := by
    intro p hp
    obtain ⟨hpmem, hpzero⟩ := Finset.mem_filter.mp hp
    rcases mul_eq_zero.mp hpzero with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hz, (Finset.mem_product.mp hpmem).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hpmem).1, Finset.mem_singleton.mpr hz⟩)
  calc
    _ ≤ (({0} : Finset R).product H ∪ H.product {0}).card := Finset.card_le_card hsub
    _ ≤ (({0} : Finset R).product H).card + (H.product {0}).card := Finset.card_union_le _ _
    _ = _ := by simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton]; omega

theorem product_kernel_sum_eq (H : Finset R) (F : R → ℝ) :
    (∑ h ∈ H, ∑ j ∈ H, F (h*j)) =
      ∑ a ∈ shiftProducts H, (((H.product H).filter (fun p => p.1*p.2=a)).card : ℝ)*F a := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := H.product H) (t := shiftProducts H) (g := fun p => p.1*p.2)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) (fun p => F (p.1*p.2))
  calc
    _ = ∑ p ∈ H.product H, F (p.1*p.2) := (Finset.sum_product H H _).symm
    _ = ∑ a ∈ shiftProducts H, ∑ p ∈ (H.product H).filter (fun p => p.1*p.2=a), F (p.1*p.2) :=
      hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ _p ∈ (H.product H).filter (fun p => p.1*p.2=a), F a := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = _ := by simp

/-- Exact finite divisor compression, keeping the degenerate shift product separate. -/
theorem product_kernel_sum_le (H : Finset R) (F : R → ℝ) (hF : ∀ a, 0 ≤ F a) (D : ℝ)
    (hD : ∀ a ∈ shiftProducts H, a ≠ 0 → ((H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card : ℝ) ≤ D) :
    (∑ h ∈ H, ∑ j ∈ H, F (h*j)) ≤
      2*(H.card : ℝ)*F 0 + D*∑ a ∈ (shiftProducts H).filter (fun a => a ≠ 0), F a := by
  rw [product_kernel_sum_eq]
  have hpoint (a) (ha : a ∈ shiftProducts H) :
      (((H.product H).filter (fun p => p.1*p.2=a)).card : ℝ)*F a ≤
        (if a=0 then 2*(H.card : ℝ)*F 0 else 0) + D*(if a≠0 then F a else 0) := by
    by_cases hz : a=0
    · subst a
      simp only [if_pos rfl, ne_eq, not_true_eq_false, if_false, mul_zero, add_zero]
      have hc : (((H.product H).filter (fun p => p.1*p.2=0)).card : ℝ) ≤ 2*(H.card : ℝ) := by
        exact_mod_cast product_zero_fiber_card_le H
      exact mul_le_mul_of_nonneg_right hc (hF 0)
    · simp only [if_neg hz, if_pos hz, zero_add]
      have hc : (((H.product H).filter (fun p => p.1*p.2=a)).card : ℝ) ≤
          ((H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card : ℝ) := by
        exact_mod_cast product_fiber_card_le_divisors H hz
      exact mul_le_mul_of_nonneg_right (hc.trans (hD a ha hz)) (hF a)
  calc
    _ ≤ ∑ a ∈ shiftProducts H,
        ((if a=0 then 2*(H.card : ℝ)*F 0 else 0) + D*(if a≠0 then F a else 0)) :=
      Finset.sum_le_sum hpoint
    _ = (if 0 ∈ shiftProducts H then 2*(H.card : ℝ)*F 0 else 0) +
        D*∑ a ∈ (shiftProducts H).filter (fun a => a ≠ 0), F a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', ← Finset.sum_filter]
    _ ≤ _ := by
      apply add_le_add_right
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (by positivity) (hF 0)

end WaringSiegel.WSL2
