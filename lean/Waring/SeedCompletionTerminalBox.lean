import Waring.SeedCompletionTerminalSparse
import Waring.SeedCompletionTerminalIdentity

/-! # The actual boxed terminal estimate with every polynomial premise discharged -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalBox
open SeedCompletionTerminalPhase SeedCompletionTerminalSparse SeedCompletionSparseWeighted
open IntegerDifferencePolynomial PolicyCompletionMajorFamily

theorem phase_magnitude_box_bound (k d : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ h m : Fin d → ℕ, (∀ i, 0 < m i) →
      (∀ i, (h i : ℝ) ≤ P^B) → (∀ i, (m i : ℝ) ≤ P^B) →
      ∀ z : ℕ, (z : ℝ) ≤ P →
        ((phase k h m z).natAbs : ℝ) ≤ P^(B*(((k+1)*k+1 : ℕ) : ℝ)) := by
  obtain ⟨P₀,hP₀,hsize⟩ := powerPolynomial_magnitude_polynomial_bound k d
  refine ⟨P₀,hP₀,?_⟩
  intro P hPP h m hm hh hmP z hz
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPQ : P ≤ P^B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hB
  have hb := hsize (P^B) (hPP.trans hPQ) (naturalParameters h m)
    (by simp) (by
      simp only [naturalParameters,List.forall_mem_ofFn_iff]
      intro i
      exact_mod_cast (hm i).ne')
    (by
      simp only [naturalParameters,List.forall_mem_ofFn_iff]
      intro i
      simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (h i)),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (m i))] using And.intro (hh i) (hmP i))
    (z : ℤ) (by simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) z)] using hz.trans hPQ)
  change ((phase k h m z).natAbs : ℝ) ≤ (P^B)^(((k+1)*k+1 : ℕ) : ℝ) at hb
  rwa [← Real.rpow_mul (zero_le_one.trans hP)] at hb

theorem padded_second_moment_box {k j r : ℕ} (hk : k ≤ 18)
    (hjk : j+r < k) (hj : 1 ≤ j)
    (hJ : 2 ≤ (k-(j+r))/2) (hjJ : j ≤ (k-(j+r))/2+1)
    {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (H A : Fin j → Finset ℕ) (G : Fin r → Finset ℕ)
        (Hcap M : Fin j → ℝ) (Gcap : Fin r → ℝ),
      (∀ i, 0 < Hcap i) → (∀ i, (H i).card ≤ Hcap i) →
      (∀ i, 0 < Gcap i) → (∀ i, (G i).card ≤ Gcap i) →
      (∀ i, ∀ h ∈ H i, 0 < h ∧ (h : ℝ) ≤ P^B) →
      (∀ i, ∀ h ∈ G i, 0 < h ∧ (h : ℝ) ≤ P^B) →
      (∀ i, ∀ m ∈ A i, 0 < m ∧ (m : ℝ) ≤ M i) →
      (∀ i, 1 ≤ M i) → (∀ i, M i ≤ P^B) → (∀ i, (A i).card ≤ M i) →
      ∀ Z : Finset ℕ, (∀ z ∈ Z, 0 < z ∧ (z : ℝ) ≤ P) → (Z.card : ℝ) ≤ P →
      paddedSecondMoment k H A G Z ≤
        C*P^ε*((P+P^(2/3 : ℝ)*(∏ i, M i)) *
          ((∏ i, Hcap i)*(∏ i, Gcap i)*(∏ i, M i))) := by
  have hrec := SeedCompletionTerminalIdentity.sparse_recognition_max hk
    (show 1 ≤ j+r by omega) hjk.le
  let L : ℝ := B*(((k+1)*k+1 : ℕ) : ℝ)
  have hL : 0 ≤ L := mul_nonneg (zero_le_one.trans hB) (Nat.cast_nonneg _)
  obtain ⟨C,hC,hbound⟩ := padded_second_moment_subpower hjk hJ hj hjJ hrec
    (zero_le_one.trans hB) hL hε
  obtain ⟨P₀,hP₀,hsize⟩ := phase_magnitude_box_bound k (j+r) hB
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H A G Hcap M Gcap hHpos hHcard hGpos hGcard hH hG hA hM hMP hAcard Z hZ hZcard
  have hP : 1 ≤ P := hP₀.trans hPP
  apply hbound P hP H A G Hcap M Gcap hHpos hHcard hGpos hGcard
    (fun i h hh => (hH i h hh).1) (fun i h hh => (hG i h hh).1)
    hA hM hMP hAcard Z hZ hZcard
  intro h hh m hm z hz
  have hhm := (mem_pi_append H G h).mp hh
  have hmm := (mem_pi_append A (fun _ : Fin r => {1}) m).mp hm
  have hmone := takeRight_eq_one A hm
  have hMB : ∀ i, 0 < m i ∧ (m i : ℝ) ≤ P^B := by
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · have hx := hA l (takeLeft m l) (Fintype.mem_piFinset.mp hmm.1 l)
      exact ⟨hx.1,hx.2.trans (hMP l)⟩
    · have he := congrFun hmone l
      change m (Fin.natAdd j l)=1 at he
      rw [he]
      exact ⟨Nat.zero_lt_one,by simpa using Real.one_le_rpow hP (zero_le_one.trans hB)⟩
  apply hsize P hPP h m (fun i => (hMB i).1) _ (fun i => (hMB i).2) z (hZ z hz).2
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · exact (hH l _ (Fintype.mem_piFinset.mp hhm.1 l)).2
  · exact (hG l _ (Fintype.mem_piFinset.mp hhm.2 l)).2

#print axioms phase_magnitude_box_bound
#print axioms padded_second_moment_box
end Waring.SeedCompletionTerminalBox
