import Waring.SeedCompletionTerminalBox
import Waring.SeedCompletionSparseWeightedDivisor

/-! # A method-independent actual terminal reduction with fixed-one padding -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalPaddedReduction
open SeedCompletionTerminalPhase SeedCompletionTerminalSecond SeedCompletionTerminalSparse
open SeedCompletionTerminalBox SeedCompletionSparseWeighted

theorem padded_second_moment_to_weighted {k j r : ℕ} (hk : k ≤ 18)
    (hjk : j+r < k) (hj : 1 ≤ j) {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (H A : Fin j → Finset ℕ) (G : Fin r → Finset ℕ),
      (∀ i, ∀ h ∈ H i, 0 < h ∧ (h : ℝ) ≤ P^B) →
      (∀ i, ∀ h ∈ G i, 0 < h ∧ (h : ℝ) ≤ P^B) →
      (∀ i, ∀ m ∈ A i, 0 < m ∧ (m : ℝ) ≤ P^B) →
      ∀ Z : Finset ℕ, (∀ z ∈ Z, 0 < z ∧ (z : ℝ) ≤ P) →
      paddedSecondMoment k H A G Z ≤
        C*P^ε*((Fintype.piFinset G).card : ℝ)*
          ((Z.card : ℝ)*
              (weightedCount H A
                (fun _ => progressionPhase (J := (k-(j+r))/2) (2*k) 2) : ℝ)+
            ((Fintype.piFinset H).card : ℝ)*((Fintype.piFinset A).card : ℝ)^2*
              (curveConstant k (j+r)*P^(2/3 : ℝ))) := by
  have hrec := SeedCompletionTerminalIdentity.sparse_recognition_max hk
    (show 1 ≤ j+r by omega) hjk.le
  let L : ℝ := B*(((k+1)*k+1 : ℕ) : ℝ)
  have hL : 0 ≤ L := mul_nonneg (zero_le_one.trans hB) (Nat.cast_nonneg _)
  obtain ⟨C,hC,hbound⟩ := source_second_moment_to_sparse hjk hrec hL hε
  obtain ⟨P₀,hP₀,hsize⟩ := phase_magnitude_box_bound k (j+r) hB
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H A G hH hG hA Z hZ
  have hP : 1 ≤ P := hP₀.trans hPP
  have hpH : ∀ i, ∀ h ∈ Fin.append H G i, 0 < h := by
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simpa only [Fin.append_left] using (fun h hh => (hH l h hh).1)
    · simpa only [Fin.append_right] using (fun h hh => (hG l h hh).1)
  have hpA : ∀ i, ∀ m ∈ Fin.append A (fun _ : Fin r => {1}) i, 0 < m := by
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simpa only [Fin.append_left] using (fun m hm => (hA l m hm).1)
    · simp only [Fin.append_right,Finset.mem_singleton]
      intro m hm
      simpa only [hm] using Nat.zero_lt_one
  have hs : ∀ h ∈ Fintype.piFinset (Fin.append H G),
      ∀ m ∈ Fintype.piFinset (Fin.append A (fun _ : Fin r => {1})), ∀ z ∈ Z,
      ((phase k h m z).natAbs : ℝ) ≤ P^L := by
    intro h hh m hm z hz
    apply hsize P hPP h m (fun i => hpA i _ (Fintype.mem_piFinset.mp hm i)) _ _ z (hZ z hz).2
    · intro i
      have hi := Fintype.mem_piFinset.mp hh i
      revert hi
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [Fin.append_left] using (fun hh => (hH l _ hh).2)
      · simpa only [Fin.append_right] using (fun hh => (hG l _ hh).2)
    · intro i
      have hi := Fintype.mem_piFinset.mp hm i
      revert hi
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [Fin.append_left] using (fun hm => (hA l _ hm).2)
      · simp only [Fin.append_right,Finset.mem_singleton]
        intro he
        rw [he]
        simpa using Real.one_le_rpow hP (zero_le_one.trans hB)
  have hb := hbound P hP (Fin.append H G) (Fin.append A (fun _ : Fin r => {1}))
    hpH hpA Z hZ hs
  rw [weightedCount_append_ones,Nat.cast_mul,card_pi_append,Nat.cast_mul,
    card_pi_append_ones] at hb
  exact hb.trans_eq (by ring)

#print axioms padded_second_moment_to_weighted
end Waring.SeedCompletionTerminalPaddedReduction
