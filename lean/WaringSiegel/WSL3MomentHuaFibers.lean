import WaringSiegel.WSL3MomentHuaPolynomial
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform finite fibers of every iterated difference

Nonzero targets force every shift to be a nonzero divisor of the target.
At zero, the degenerate shift tuples lose one free coordinate.  The bounds
retain that loss exactly, as required by Hua's induction.
-/

noncomputable section
open Finset Polynomial
open scoped BigOperators Classical

namespace WaringSiegel.WSL3
open WSL2

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

def iteratedDifferenceFiber (S H : Finset R) (k J : ℕ) (a : R) :
    Finset ((Fin J → R) × R) :=
  ((Fintype.piFinset fun _ : Fin J => H).product S).filter
    (fun t => (iteratedPolynomialDifference (X ^ k) J t.1).eval t.2 = a)

/-- Fixed nonzero shifts leave at most k−J base points, for any selected
subfamily of solutions. -/
theorem iteratedDifference_selected_card_le (S D : Finset R) (k J : ℕ) (hJ : J < k)
    (a : R) (T : Finset ((Fin J → R) × R))
    (hT : ∀ t ∈ T, t.2 ∈ S ∧ (∀ i, t.1 i ∈ D ∧ t.1 i ≠ 0) ∧
      (iteratedPolynomialDifference (X ^ k) J t.1).eval t.2 = a) :
    T.card ≤ (k - J) * D.card ^ J := by
  have hi : T.image Prod.fst ⊆ Fintype.piFinset (fun _ : Fin J => D) := by
    intro h hh
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hh
    exact Fintype.mem_piFinset.mpr (fun i => ((hT t ht).2.1 i).1)
  have hfiber (h : Fin J → R) (hh : h ∈ T.image Prod.fst) :
      (T.filter (fun t => t.1 = h)).card ≤ k - J := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hh
    have hcard : (T.filter (fun u => u.1 = t.1)).card ≤
        (S.filter (fun x => (iteratedPolynomialDifference (X ^ k) J t.1).eval x = a)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro u hu
        obtain ⟨huT, hu⟩ := Finset.mem_filter.mp hu
        refine Finset.mem_filter.mpr ⟨(hT u huT).1, ?_⟩
        simpa only [hu] using (hT u huT).2.2
      · intro u hu v hv heq
        exact Prod.ext (((Finset.mem_filter.mp hu).2).trans (Finset.mem_filter.mp hv).2.symm) heq
    exact hcard.trans (iteratedPowerDifference_fiber_card_le S k J hJ t.1
      (fun i => ((hT t ht).2.1 i).2) a)
  calc
    T.card ≤ (k - J) * (T.image Prod.fst).card :=
      Finset.card_le_mul_card_image T (k - J) hfiber
    _ ≤ (k - J) * (Fintype.piFinset (fun _ : Fin J => D)).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card hi)
    _ = _ := by rw [Fintype.card_piFinset_const]

theorem iteratedDifference_fiber_card_le_divisors (S H : Finset R) (k J : ℕ) (hJ : J < k)
    {a : R} (ha : a ≠ 0) :
    (iteratedDifferenceFiber S H k J a).card ≤
      (k - J) * (H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card ^ J := by
  apply iteratedDifference_selected_card_le S _ k J hJ a
  intro t ht
  obtain ⟨htHS, heval⟩ := Finset.mem_filter.mp ht
  obtain ⟨hh, hx⟩ := Finset.mem_product.mp htHS
  refine ⟨hx, ?_, heval⟩
  intro i
  have hnz : t.1 i ≠ 0 := by
    intro hz
    have hp := iteratedPolynomialDifference_eq_zero_of_shift_zero (X ^ k) J t.1 i hz
    rw [hp, eval_zero] at heval
    exact ha heval.symm
  refine ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hh i, hnz, ?_⟩, hnz⟩
  rw [← heval]
  exact iteratedPolynomialDifference_shift_dvd_eval _ _ _ _ _

theorem iteratedDifference_nonzero_shifts_card_le (S H : Finset R) (k J : ℕ) (hJ : J < k)
    (a : R) :
    ((iteratedDifferenceFiber S H k J a).filter (fun t => ∀ i, t.1 i ≠ 0)).card ≤
      (k - J) * H.card ^ J := by
  apply iteratedDifference_selected_card_le S H k J hJ a
  intro t ht
  obtain ⟨htF, hnz⟩ := Finset.mem_filter.mp ht
  obtain ⟨htHS, heval⟩ := Finset.mem_filter.mp htF
  obtain ⟨hh, hx⟩ := Finset.mem_product.mp htHS
  exact ⟨hx, fun i => ⟨Fintype.mem_piFinset.mp hh i, hnz i⟩, heval⟩

/-- A tuple having at least one zero coordinate has at most J choices of
the zero position and J−1 free coordinates. -/
theorem shift_tuples_with_zero_card_le (H : Finset R) (J : ℕ) :
    ((Fintype.piFinset fun _ : Fin J => H).filter (fun h => ∃ i, h i = 0)).card ≤
      J * H.card ^ (J - 1) := by
  let A := Fintype.piFinset (fun _ : Fin J => H)
  have hsub : A.filter (fun h => ∃ i, h i = 0) ⊆
      Finset.univ.biUnion (fun i : Fin J => A.filter (fun h => h i = 0)) := by
    intro h hh
    obtain ⟨hhA, i, hi⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hhA, hi⟩⟩
  have hcard (i : Fin J) : (A.filter (fun h => h i = 0)).card ≤ H.card ^ (J - 1) := by
    by_cases hz : (0 : R) ∈ H
    · exact le_of_eq (by
        simpa only [Fintype.card_fin] using Fintype.card_filter_piFinset_const_eq_of_mem H i hz)
    · have he : A.filter (fun h => h i = 0) = ∅ :=
        Fintype.filter_piFinset_of_notMem _ i 0 hz
      rw [he, Finset.card_empty]
      exact Nat.zero_le _
  calc
    _ ≤ (Finset.univ.biUnion (fun i : Fin J => A.filter (fun h => h i = 0))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i : Fin J, (A.filter (fun h => h i = 0)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin J, H.card ^ (J - 1) := Finset.sum_le_sum (fun i _ => hcard i)
    _ = _ := by simp

theorem iteratedDifference_zero_fiber_card_le (S H : Finset R) (k J : ℕ) (hJ : J < k) :
    (iteratedDifferenceFiber S H k J 0).card ≤
      J * H.card ^ (J - 1) * S.card + (k - J) * H.card ^ J := by
  let F := iteratedDifferenceFiber S H k J (0 : R)
  let bad := F.filter (fun t => ∃ i, t.1 i = 0)
  let good := F.filter (fun t => ∀ i, t.1 i ≠ 0)
  have hF : F ⊆ bad ∪ good := by
    intro t ht
    by_cases hz : ∃ i, t.1 i = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, by simpa using hz⟩)
  have hbad : bad.card ≤ J * H.card ^ (J - 1) * S.card := by
    have hb : bad ⊆ ((Fintype.piFinset fun _ : Fin J => H).filter
        (fun h => ∃ i, h i = 0)).product S := by
      intro t ht
      obtain ⟨htF, hz⟩ := Finset.mem_filter.mp ht
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp htF).1
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm.1, hz⟩, hm.2⟩
    exact (Finset.card_le_card hb).trans (by
      rw [Finset.product_eq_sprod, Finset.card_product]
      exact Nat.mul_le_mul_right S.card (shift_tuples_with_zero_card_le H J))
  have hgood : good.card ≤ (k - J) * H.card ^ J :=
    iteratedDifference_nonzero_shifts_card_le S H k J hJ 0
  exact (Finset.card_le_card hF).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hbad hgood))

#print axioms iteratedDifference_fiber_card_le_divisors
#print axioms iteratedDifference_zero_fiber_card_le

end WaringSiegel.WSL3
