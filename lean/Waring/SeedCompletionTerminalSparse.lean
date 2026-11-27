import Waring.SeedCompletionTerminalSecond
import Waring.SeedCompletionSparseWeightedPadding

/-! # Sharp terminal energy with arbitrary extra fixed-one differences -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalSparse
open SeedCompletionTerminalPhase SeedCompletionTerminalSecond SeedCompletionSparseWeighted

theorem pi_card_le {s : ℕ} (A : Fin s → Finset ℕ) (M : Fin s → ℝ)
    (hM : ∀ i, ((A i).card : ℝ) ≤ M i) :
    ((Fintype.piFinset A).card : ℝ) ≤ ∏ i, M i := by
  simp only [Fintype.card_piFinset,Nat.cast_prod]
  exact Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hM i)

theorem card_pi_append {s t : ℕ} (A : Fin s → Finset ℕ) (B : Fin t → Finset ℕ) :
    (Fintype.piFinset (Fin.append A B)).card =
      (Fintype.piFinset A).card * (Fintype.piFinset B).card := by
  simp only [Fintype.card_piFinset,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem card_pi_append_ones {s t : ℕ} (A : Fin s → Finset ℕ) :
    (Fintype.piFinset (Fin.append A (fun _ : Fin t => {1}))).card =
      (Fintype.piFinset A).card := by
  rw [card_pi_append]
  simp [Fintype.card_piFinset]

theorem scale_split_bound {P ε C₀ C₁ C₂ X Y : ℝ}
    (hP : 1 ≤ P) (hε : 0 < ε) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    C₀*P^(ε/2)*(C₁*P^(ε/2)*X+C₂*Y) ≤
      (C₀*(C₁+C₂))*P^ε*(X+Y) := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have he : 1 ≤ P^(ε/2) := Real.one_le_rpow hP (by positivity)
  have hCsum : 0 ≤ C₁+C₂ := add_nonneg hC₁ hC₂
  have hc1 : C₁*P^(ε/2) ≤ (C₁+C₂)*P^(ε/2) := by gcongr; linarith
  have hc2 : C₂ ≤ (C₁+C₂)*P^(ε/2) := by
    calc
      _ ≤ C₁+C₂ := by linarith
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left he hCsum]
  have hp : P^(ε/2)*P^(ε/2)=P^ε := by
    rw [← Real.rpow_add hPp]
    congr 1
    ring
  calc
    _ ≤ C₀*P^(ε/2)*((C₁+C₂)*P^(ε/2)*X+(C₁+C₂)*P^(ε/2)*Y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_right hc1 hX) (mul_le_mul_of_nonneg_right hc2 hY)
    _ = (C₀*(C₁+C₂))*(P^(ε/2)*P^(ε/2))*(X+Y) := by ring
    _ = _ := by rw [hp]

def paddedSecondMoment {j r : ℕ} (k : ℕ) (H A : Fin j → Finset ℕ)
    (G : Fin r → Finset ℕ) (Z : Finset ℕ) : ℝ :=
  sourceSecondMoment k (Fintype.piFinset (Fin.append H G))
    (Fintype.piFinset (Fin.append A (fun _ => {1}))) Z

theorem padded_second_moment_subpower {k j r J : ℕ}
    (hjk : j+r < k) (hJ : 2 ≤ J) (hj : 1 ≤ j) (hjJ : j ≤ J+1)
    (hrec : SparseRecognition k (j+r) J) {B L ε : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (H A : Fin j → Finset ℕ) (G : Fin r → Finset ℕ)
        (Hcap M : Fin j → ℝ) (Gcap : Fin r → ℝ),
      (∀ i, 0 < Hcap i) → (∀ i, (H i).card ≤ Hcap i) →
      (∀ i, 0 < Gcap i) → (∀ i, (G i).card ≤ Gcap i) →
      (∀ i, ∀ h ∈ H i, 0 < h) → (∀ i, ∀ h ∈ G i, 0 < h) →
      (∀ i, ∀ m ∈ A i, 0 < m ∧ (m : ℝ) ≤ M i) →
      (∀ i, 1 ≤ M i) → (∀ i, M i ≤ P^B) → (∀ i, (A i).card ≤ M i) →
      ∀ Z : Finset ℕ, (∀ z ∈ Z, 0 < z ∧ (z : ℝ) ≤ P) → (Z.card : ℝ) ≤ P →
      (∀ h ∈ Fintype.piFinset (Fin.append H G),
        ∀ m ∈ Fintype.piFinset (Fin.append A (fun _ : Fin r => {1})), ∀ z ∈ Z,
        ((phase k h m z).natAbs : ℝ) ≤ P^L) →
      paddedSecondMoment k H A G Z ≤
        C*P^ε*((P+P^(2/3 : ℝ)*(∏ i, M i)) *
          ((∏ i, Hcap i)*(∏ i, Gcap i)*(∏ i, M i))) := by
  obtain ⟨C₀,hC₀,hsource⟩ := source_second_moment_to_sparse hjk hrec hL
    (show 0 < ε/2 by positivity)
  obtain ⟨C₁,hC₁,hweight⟩ := weighted_even_progression_subpower k J j (by omega)
    hJ hj hjJ hB (show 0 < ε/2 by positivity)
  let C₂ := curveConstant k (j+r)
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂,curveConstant]; positivity
  refine ⟨C₀*(C₁+C₂),mul_pos hC₀ (by linarith),?_⟩
  intro P hP H A G Hcap M Gcap hHpos hHcard hGpos hGcard hH hG hA hM hMP hAcard Z hZ hZcard hsize
  let U : ℝ := ∏ i, Hcap i
  let V : ℝ := ∏ i, Gcap i
  let Q : ℝ := ∏ i, M i
  have hU : 0 ≤ U := Finset.prod_nonneg (fun i _ => (hHpos i).le)
  have hV : 0 ≤ V := Finset.prod_nonneg (fun i _ => (hGpos i).le)
  have hQ : 0 ≤ Q := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hM i))
  have hHC : ((Fintype.piFinset H).card : ℝ) ≤ U := pi_card_le H Hcap hHcard
  have hGC : ((Fintype.piFinset G).card : ℝ) ≤ V := pi_card_le G Gcap hGcard
  have hAC : ((Fintype.piFinset A).card : ℝ) ≤ Q := pi_card_le A M hAcard
  have hweight' := hweight P hP H A Hcap M hHpos hHcard hH hM hMP
    (fun i m hm => (hA i m hm).2) hAcard
  have hwfull :
      (weightedCount (Fin.append H G) (Fin.append A (fun _ : Fin r => {1}))
        (fun _ => progressionPhase (J := J) (2*k) 2) : ℝ) ≤
      C₁*P^(ε/2)*(U*V*Q) := by
    rw [weightedCount_append_ones,Nat.cast_mul]
    apply (mul_le_mul hGC hweight' (Nat.cast_nonneg _) hV).trans_eq
    simp only [Finset.prod_mul_distrib]
    dsimp [U,V,Q]
    ring
  have hHH : ((Fintype.piFinset (Fin.append H G)).card : ℝ) ≤ U*V := by
    rw [card_pi_append,Nat.cast_mul]
    exact mul_le_mul hHC hGC (Nat.cast_nonneg _) hU
  have hAA : ((Fintype.piFinset (Fin.append A (fun _ : Fin r => {1}))).card : ℝ) ≤ Q := by
    rw [card_pi_append_ones]
    exact hAC
  have hb := hsource P hP (Fin.append H G) (Fin.append A (fun _ : Fin r => {1}))
    (by
      intro i
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [Fin.append_left] using hH l
      · simpa only [Fin.append_right] using hG l)
    (by
      intro i
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [Fin.append_left] using (fun m hm => (hA l m hm).1)
      · simp only [Fin.append_right,Finset.mem_singleton]
        intro m hm
        simpa only [hm] using Nat.zero_lt_one)
    Z hZ hsize
  apply hb.trans
  calc
    _ ≤ C₀*P^(ε/2)*(P*(C₁*P^(ε/2)*(U*V*Q))+
        (U*V)*Q^2*(C₂*P^(2/3 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul hZcard hwfull (Nat.cast_nonneg _) (zero_le_one.trans hP)
      · dsimp [C₂]
        gcongr
    _ = C₀*P^(ε/2)*(C₁*P^(ε/2)*(P*U*V*Q)+C₂*(P^(2/3 : ℝ)*U*V*Q^2)) := by ring
    _ ≤ (C₀*(C₁+C₂))*P^ε*((P*U*V*Q)+(P^(2/3 : ℝ)*U*V*Q^2)) :=
      scale_split_bound hP hε hC₀.le hC₁.le hC₂ (by positivity) (by positivity)
    _ = _ := by dsimp [U,V,Q]; ring

#print axioms padded_second_moment_subpower
end Waring.SeedCompletionTerminalSparse
