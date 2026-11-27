import Waring.SeedCompletionTerminalPhase
import Waring.SeedCompletionTerminalCurves
import Waring.SeedCompletionSparseWeighted

/-! # Reduction of the literal source second moment to its sparse diagonal -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalSecond
open SeedCompletionTerminalPhase SeedCompletionTerminalCurves
open SeedCompletionSparseWeighted IntegerDifferencePolynomial PolicyCompletionMajorFamily

def SparseRecognition (k j J : ℕ) : Prop :=
  ∀ h m n : Fin j → ℕ, (∀ i, 0 < h i) → (∀ i, 0 < m i) → (∀ i, 0 < n i) →
    powerPolynomial k (naturalParameters h m)=powerPolynomial k (naturalParameters h n) →
    ∀ r : Fin J,
      (∑ i, (h i : ℤ)^(2*(r.val+1))*(m i : ℤ)^(2*k*(r.val+1))) =
      ∑ i, (h i : ℤ)^(2*(r.val+1))*(n i : ℤ)^(2*k*(r.val+1))

def sourceSecondMoment {j : ℕ} (k : ℕ) (H B : Finset (Fin j → ℕ))
    (Z : Finset ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖∑ x ∈ H ×ˢ (B ×ˢ Z),
    fourier (phase k x.1 x.2.1 x.2.2) (α : AddCircle (1 : ℝ))‖^2

def curveConstant (k j : ℕ) : ℝ :=
  ((k-j : ℕ) : ℝ)*(8*((k-j : ℕ) : ℝ)^2+3)

theorem samePolynomialPairs_le_vector {k j J : ℕ} (hrec : SparseRecognition k j J)
    (h : Fin j → ℕ) (hh : ∀ i, 0 < h i) (A : Fin j → Finset ℕ)
    (hA : ∀ i, ∀ m ∈ A i, 0 < m) :
    (samePolynomialPairs (Fintype.piFinset A) (realPolynomial k h)).card ≤
      (vectorCollision A (fun i => progressionPhase (J := J) (2*k) 2 (h i))).card := by
  classical
  apply Finset.card_le_card
  intro mn hmn
  obtain ⟨hmn,he⟩ := Finset.mem_filter.mp hmn
  obtain ⟨hm,hn⟩ := Finset.mem_product.mp hmn
  have heZ : powerPolynomial k (naturalParameters h mn.1)=
      powerPolynomial k (naturalParameters h mn.2) :=
    Polynomial.map_injective (Int.castRingHom ℝ) (Int.cast_injective (α := ℝ)) he
  have hs := hrec h mn.1 mn.2 hh
    (fun i => hA i _ (Fintype.mem_piFinset.mp hm i))
    (fun i => hA i _ (Fintype.mem_piFinset.mp hn i)) heZ
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm,hn⟩,?_⟩
  funext r
  simpa only [vectorFrequency,Finset.sum_apply,progressionPhase] using hs r

theorem source_second_moment_to_sparse {k j J : ℕ} (hj : j < k)
    (hrec : SparseRecognition k j J) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H A : Fin j → Finset ℕ,
      (∀ i, ∀ h ∈ H i, 0 < h) → (∀ i, ∀ m ∈ A i, 0 < m) →
      ∀ Z : Finset ℕ, (∀ z ∈ Z, 0 < z ∧ (z : ℝ) ≤ P) →
      (∀ h ∈ Fintype.piFinset H, ∀ m ∈ Fintype.piFinset A, ∀ z ∈ Z,
        ((phase k h m z).natAbs : ℝ) ≤ P^L) →
      sourceSecondMoment k (Fintype.piFinset H) (Fintype.piFinset A) Z ≤
        C*P^ε*((Z.card : ℝ)*
          (weightedCount H A (fun _ => progressionPhase (J := J) (2*k) 2) : ℝ) +
          ((Fintype.piFinset H).card : ℝ)*((Fintype.piFinset A).card : ℝ)^2*
            (curveConstant k j*P^(2/3 : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := second_moment_diagonal_and_curve (j := j) hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H A hH hA Z hZ hsize
  have hhpos (h : Fin j → ℕ) (hh : h ∈ Fintype.piFinset H) (i : Fin j) : 0 < h i :=
    hH i _ (Fintype.mem_piFinset.mp hh i)
  have hmpos (m : Fin j → ℕ) (hm : m ∈ Fintype.piFinset A) (i : Fin j) : 0 < m i :=
    hA i _ (Fintype.mem_piFinset.mp hm i)
  have hb := hbound P hP (Fin j → ℕ) (Fintype.piFinset H) (Fintype.piFinset A) Z
    (phase k) (realPolynomial k) (k-j) ((-1 : ℝ)^(k+j)) (by omega) (parity_square k j)
    (fun h hh m hm => realPolynomial_natDegree hj.le h m (hhpos h hh) (hmpos m hm))
    (by
      intro h hh m hm n hn
      rw [realPolynomial_leadingCoeff hj.le h m (hhpos h hh) (hmpos m hm),
        realPolynomial_leadingCoeff hj.le h n (hhpos h hh) (hmpos n hn)])
    (fun h hh m hm z => realPolynomial_parity k h m (hmpos m hm) z)
    (fun h hh m hm => phase_strictMono hj h m (hhpos h hh) (hmpos m hm))
    (fun h _ m _ z => realPolynomial_eval k h m z)
    (fun z hz => (hZ z hz).2)
    (fun h hh m hm z hz => ⟨(phase_pos hj h m (hhpos h hh) (hmpos m hm) (hZ z hz).1).ne',
      hsize h hh m hm z hz⟩)
    (fun h _ m hm z _ i => height_dvd_phase k h m (hmpos m hm) z i)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Z.card)
  simp only [weightedCount,Nat.cast_sum]
  apply Finset.sum_le_sum
  intro h hh
  exact_mod_cast samePolynomialPairs_le_vector hrec h (hhpos h hh) A hA

#print axioms source_second_moment_to_sparse
end Waring.SeedCompletionTerminalSecond
