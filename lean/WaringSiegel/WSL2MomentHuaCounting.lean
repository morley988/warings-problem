import WaringSiegel.WSL2MomentHuaPolynomial

/-!
# Literal finite triple counts for the second Hua difference

The two shifts and base point are counted in their original integral domain.
A nonzero target forces both shifts to be nonzero divisors of that target;
with shifts fixed, polynomial root counting supplies at most k−2 base points.
-/

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL2
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- The literal two-shift finite-difference fiber. -/
def doubleDifferenceFiber (S H : Finset R) (k : ℕ) (a : R) : Finset (R × (R × R)) :=
  (H.product (H.product S)).filter (fun t =>
    (polynomialDifference t.1 (polynomialDifference t.2.1 (X ^ k))).eval t.2.2 = a)

/-- Fixed nonzero shifts leave at most k−2 possible base points. -/
theorem doubleDifference_shift_fiber_card_le (S H : Finset R) (k : ℕ) (hk : 3 ≤ k)
    (a h₁ h₂ : R) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
    ((doubleDifferenceFiber S H k a).filter (fun t => (t.1, t.2.1) = (h₁, h₂))).card ≤ k - 2 := by
  let T := (doubleDifferenceFiber S H k a).filter (fun t => (t.1, t.2.1) = (h₁, h₂))
  have hcard : T.card ≤ (S.filter (fun x =>
      (polynomialDifference h₁ (polynomialDifference h₂ (X ^ k))).eval x = a)).card := by
    apply Finset.card_le_card_of_injOn (fun t : R × (R × R) => t.2.2)
    · intro t ht
      obtain ⟨htF, htpair⟩ := Finset.mem_filter.mp ht
      obtain ⟨htHS, hteval⟩ := Finset.mem_filter.mp htF
      have ht₁ : t.1 = h₁ := congrArg Prod.fst htpair
      have ht₂ : t.2.1 = h₂ := congrArg Prod.snd htpair
      refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_product.mp htHS).2).2, ?_⟩
      simpa only [ht₁, ht₂] using hteval
    · intro t ht u hu he
      have ht' := (Finset.mem_filter.mp ht).2
      have hu' := (Finset.mem_filter.mp hu).2
      apply Prod.ext
      · exact (congrArg Prod.fst ht').trans (congrArg Prod.fst hu').symm
      · exact Prod.ext ((congrArg Prod.snd ht').trans (congrArg Prod.snd hu').symm) he
  exact hcard.trans (double_powerDifference_fiber_card_le S k hk h₂ h₁ hh₂ hh₁ a)

/-- Every nonzero double-difference target forces both shifts to be actual
nonzero ring divisors of that target. -/
theorem doubleDifference_shifts_mem_divisors (S H : Finset R) (k : ℕ)
    {a : R} (ha : a ≠ 0) {t : R × (R × R)} (ht : t ∈ doubleDifferenceFiber S H k a) :
    (t.1, t.2.1) ∈ (H.filter (fun h => h ≠ 0 ∧ h ∣ a)).product
      (H.filter (fun h => h ≠ 0 ∧ h ∣ a)) := by
  obtain ⟨htHS, hteval⟩ := Finset.mem_filter.mp ht
  have htmem := Finset.mem_product.mp htHS
  have hnz : t.1 ≠ 0 ∧ t.2.1 ≠ 0 := by
    constructor
    · intro hz
      apply ha
      rw [hz, polynomialDifference_zero, eval_zero] at hteval
      exact hteval.symm
    · intro hz
      apply ha
      rw [hz, polynomialDifference_zero, polynomialDifference_zero_polynomial, eval_zero] at hteval
      exact hteval.symm
  apply Finset.mem_product.mpr
  constructor
  · refine Finset.mem_filter.mpr ⟨htmem.1, hnz.1, ?_⟩
    rw [← hteval]
    exact double_polynomialDifference_right_dvd_eval _ _ _ _
  · refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp htmem.2).1, hnz.2, ?_⟩
    rw [← hteval]
    exact double_polynomialDifference_left_dvd_eval _ _ _ _

/-- Exact finite divisor reduction for every nonzero double-difference target. -/
theorem doubleDifference_fiber_card_le_divisors (S H : Finset R) (k : ℕ) (hk : 3 ≤ k)
    {a : R} (ha : a ≠ 0) :
    (doubleDifferenceFiber S H k a).card ≤
      (k - 2) * (H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card ^ 2 := by
  let T := doubleDifferenceFiber S H k a
  let D := H.filter (fun h => h ≠ 0 ∧ h ∣ a)
  have hi : T.image (fun t => (t.1, t.2.1)) ⊆ D.product D := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact doubleDifference_shifts_mem_divisors S H k ha ht
  calc
    T.card ≤ (k - 2) * (T.image (fun t => (t.1, t.2.1))).card := by
      apply Finset.card_le_mul_card_image T (k - 2)
      intro p hp
      have hm := Finset.mem_product.mp (hi hp)
      exact doubleDifference_shift_fiber_card_le S H k hk a p.1 p.2
        (Finset.mem_filter.mp hm.1).2.1 (Finset.mem_filter.mp hm.2).2.1
    _ ≤ (k - 2) * (D.product D).card := Nat.mul_le_mul_left _ (Finset.card_le_card hi)
    _ = _ := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

/-- The part with both shifts nonzero is bounded for every target, including zero. -/
theorem doubleDifference_nonzero_shifts_card_le (S H : Finset R) (k : ℕ) (hk : 3 ≤ k) (a : R) :
    ((doubleDifferenceFiber S H k a).filter (fun t => t.1 ≠ 0 ∧ t.2.1 ≠ 0)).card ≤
      (k - 2) * H.card ^ 2 := by
  let T := (doubleDifferenceFiber S H k a).filter (fun t => t.1 ≠ 0 ∧ t.2.1 ≠ 0)
  have hi : T.image (fun t => (t.1, t.2.1)) ⊆ H.product H := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
    exact Finset.mem_product.mpr ⟨hh.1, (Finset.mem_product.mp hh.2).1⟩
  calc
    T.card ≤ (k - 2) * (T.image (fun t => (t.1, t.2.1))).card := by
      apply Finset.card_le_mul_card_image T (k - 2)
      intro p hp
      obtain ⟨t, ht, htP⟩ := Finset.mem_image.mp hp
      have hnz := (Finset.mem_filter.mp ht).2
      have hp₁ : p.1 ≠ 0 := by simpa only [← htP] using hnz.1
      have hp₂ : p.2 ≠ 0 := by simpa only [← htP] using hnz.2
      have hsub : T.filter (fun t => (t.1, t.2.1) = p) ⊆
          (doubleDifferenceFiber S H k a).filter (fun t => (t.1, t.2.1) = p) := by
        intro z hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1,
          (Finset.mem_filter.mp hz).2⟩
      exact (Finset.card_le_card hsub).trans
        (doubleDifference_shift_fiber_card_le S H k hk a p.1 p.2 hp₁ hp₂)
    _ ≤ (k - 2) * (H.product H).card := Nat.mul_le_mul_left _ (Finset.card_le_card hi)
    _ = _ := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

/-- At zero, the two degenerate shift families contribute at most 2|H||S|. -/
theorem doubleDifference_zero_fiber_card_le (S H : Finset R) (k : ℕ) (hk : 3 ≤ k) :
    (doubleDifferenceFiber S H k 0).card ≤ 2 * H.card * S.card + (k - 2) * H.card ^ 2 := by
  let F := doubleDifferenceFiber S H k (0 : R)
  let bad := F.filter (fun t => t.1 = 0 ∨ t.2.1 = 0)
  let good := F.filter (fun t => t.1 ≠ 0 ∧ t.2.1 ≠ 0)
  have hFsub : F ⊆ bad ∪ good := by
    intro t ht
    by_cases hz : t.1 = 0 ∨ t.2.1 = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, not_or.mp hz⟩)
  have hbsub : bad ⊆ ({0} : Finset R).product (H.product S) ∪
      H.product (({0} : Finset R).product S) := by
    intro t ht
    obtain ⟨htF, hzero⟩ := Finset.mem_filter.mp ht
    have hmem := Finset.mem_product.mp (Finset.mem_filter.mp htF).1
    rcases hzero with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hz, hmem.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨hmem.1, Finset.mem_product.mpr
          ⟨Finset.mem_singleton.mpr hz, (Finset.mem_product.mp hmem.2).2⟩⟩)
  have hbad : bad.card ≤ 2 * H.card * S.card := by
    calc
      _ ≤ (({0} : Finset R).product (H.product S) ∪
          H.product (({0} : Finset R).product S)).card := Finset.card_le_card hbsub
      _ ≤ (({0} : Finset R).product (H.product S)).card +
          (H.product (({0} : Finset R).product S)).card := Finset.card_union_le _ _
      _ = _ := by simp only [Finset.product_eq_sprod, Finset.card_product,
        Finset.card_singleton, one_mul]; ring
  have hgood : good.card ≤ (k - 2) * H.card ^ 2 :=
    doubleDifference_nonzero_shifts_card_le S H k hk 0
  exact (Finset.card_le_card hFsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hbad hgood))

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.doubleDifference_fiber_card_le_divisors
#print axioms WaringSiegel.WSL2.doubleDifference_zero_fiber_card_le
