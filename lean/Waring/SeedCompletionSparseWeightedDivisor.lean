import Waring.SeedCompletionSparseWeightedPadding
import Waring.AuxiliaryTupleCount

/-! # The alternative weighted diagonal estimate by exact divisor elimination -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted
open AuxiliaryTupleCount AuxiliaryCounting

theorem weightedCount_le_auxiliary {k j J : ℕ} (hJ : 1 ≤ J)
    (H A : Fin j → Finset ℕ) (Hbound Mbound : ℕ → ℕ)
    (hH : ∀ i, H i ⊆ Finset.Icc 1 (Hbound i.val))
    (hA : ∀ i, A i ⊆ Finset.Icc 1 (Mbound i.val)) :
    weightedCount H A (fun _ => progressionPhase (J := J) (2*k) 2) ≤
      zeroCount (2*k) (prefixFamily Hbound Mbound j) := by
  classical
  have hHsub : Fintype.piFinset H ⊆ coordinateBox Hbound j := by
    exact Fintype.piFinset_subset _ _ hH
  have hAsub : Fintype.piFinset A ⊆ coordinateBox Mbound j := by
    exact Fintype.piFinset_subset _ _ hA
  apply le_trans _ (vector_collision_count_le (2*k) j Hbound Mbound)
  calc
    _ ≤ ∑ h ∈ Fintype.piFinset H,
        (((coordinateBox Mbound j) ×ˢ (coordinateBox Mbound j)).filter (fun mn =>
          ∑ i : Fin j, (h i : ℤ)^2*((mn.1 i : ℤ)^(2*k)-(mn.2 i : ℤ)^(2*k))=0)).card := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.card_le_card
      intro mn hmn
      obtain ⟨hmn,he⟩ := Finset.mem_filter.mp hmn
      refine Finset.mem_filter.mpr ⟨Finset.product_subset_product hAsub hAsub hmn,?_⟩
      have hr := congrFun he (⟨0,by omega⟩ : Fin J)
      simp only [vectorFrequency,Finset.sum_apply,progressionPhase,Nat.zero_add,Nat.mul_one] at hr
      simpa only [mul_sub,Finset.sum_sub_distrib] using sub_eq_zero.mpr hr
    _ ≤ ∑ h ∈ coordinateBox Hbound j,
        (((coordinateBox Mbound j) ×ˢ (coordinateBox Mbound j)).filter (fun mn =>
          ∑ i : Fin j, (h i : ℤ)^2*((mn.1 i : ℤ)^(2*k)-(mn.2 i : ℤ)^(2*k))=0)).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hHsub (fun _ _ _ => Nat.zero_le _)

theorem weighted_divisor_subpower (j J : ℕ) (hJ : 1 ≤ J) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ k : ℕ, 1 ≤ k →
      ∀ (H A : Fin j → Finset ℕ) (Hbound Mbound : ℕ → ℕ),
      (∀ i, H i ⊆ Finset.Icc 1 (Hbound i.val)) →
      (∀ i, A i ⊆ Finset.Icc 1 (Mbound i.val)) →
      (∀ i < j, ((Hbound i^2*(Mbound i)^(2*k) : ℕ) : ℝ) ≤ P^B) →
      (∀ i < j, (∏ l ∈ Finset.range i, Mbound l) ≤ Hbound i*Mbound i) →
      (weightedCount H A (fun _ => progressionPhase (J := J) (2*k) 2) : ℝ) ≤
        C*P^ε*(diagonalProduct Hbound Mbound j : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := auxiliary_zeroCount_le_polynomial j hB hε
  refine ⟨C,hC,?_⟩
  intro P hP k hk H A Hbound Mbound hH hA hsize hparam
  apply le_trans _ (hbound P hP (2*k) (by omega) Hbound Mbound hsize hparam)
  exact_mod_cast weightedCount_le_auxiliary (k := k) hJ H A Hbound Mbound hH hA

#print axioms weightedCount_le_auxiliary
#print axioms weighted_divisor_subpower
end Waring.SeedCompletionSparseWeighted
