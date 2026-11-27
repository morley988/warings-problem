import Waring.PolicyCompletionSharpResidualPadded
import Waring.SeedCompletionTerminalDivisorBox

/-! # Sharp padded source energy under the elementary prefix product conditions -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionSharpResidualDivisorBox
open SeedCompletionTerminalPhase SeedCompletionTerminalSecond SeedCompletionTerminalSparse
open PolicyCompletionSharpResidualPadded PolicyCompletionSharpResidualSource
open SeedCompletionSparseWeighted SeedCompletionTerminalDivisorBox
open AuxiliaryTupleCount AuxiliaryCounting

theorem sharp_padded_second_moment_divisor_box {k j r : ℕ} (hk : k ≤ 18)
    (hjk : j+r+2 ≤ k) (hj : 1 ≤ j) (hgood : SharpResidual k (j+r)) {B L ε : ℝ}
    (hB : 1 ≤ B) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (H A : Fin j → Finset ℕ) (G : Fin r → Finset ℕ) (Hbound Mbound : ℕ → ℕ),
      (∀ i, H i ⊆ Finset.Icc 1 (Hbound i.val)) →
      (∀ i, A i ⊆ Finset.Icc 1 (Mbound i.val)) →
      (∀ i < j, (Hbound i : ℝ) ≤ P^B ∧ (Mbound i : ℝ) ≤ P^B) →
      (∀ i < j, ((Hbound i^2*(Mbound i)^(2*k) : ℕ) : ℝ) ≤ P^L) →
      (∀ i < j, (∏ l ∈ Finset.range i, Mbound l) ≤ Hbound i*Mbound i) →
      (∀ i, ∀ h ∈ G i, 0 < h ∧ (h : ℝ) ≤ P^B) →
      ∀ Z : Finset ℕ, (∀ z ∈ Z, 0 < z ∧ (z : ℝ) ≤ P) → (Z.card : ℝ) ≤ P →
      paddedSecondMoment k H A G Z ≤
        C*P^ε*(P+((coordinateBox Mbound j).card : ℝ))*
          (diagonalProduct Hbound Mbound j : ℝ)*((Fintype.piFinset G).card : ℝ) := by
  have hJ : 1 ≤ (k-(j+r))/2 := by omega
  obtain ⟨C₀,hC₀,P₀,hP₀,hsource⟩ := sharp_padded_second_moment_to_weighted hk
    (show j+r < k by omega) hj hgood hB (show 0 < ε/2 by positivity)
  obtain ⟨C₁,hC₁,hweight⟩ := weighted_divisor_subpower j ((k-(j+r))/2) hJ hL
    (show 0 < ε/2 by positivity)
  let C₂ : ℝ := 1
  have hC₂ : 0 ≤ C₂ := by norm_num [C₂]
  refine ⟨C₀*(C₁+C₂),mul_pos hC₀ (by linarith),P₀,hP₀,?_⟩
  intro P hPP H A G Hbound Mbound hH hA hbox hsize hparam hG Z hZ hZcard
  have hP : 1 ≤ P := hP₀.trans hPP
  have hHs : Fintype.piFinset H ⊆ coordinateBox Hbound j := Fintype.piFinset_subset _ _ hH
  have hAs : Fintype.piFinset A ⊆ coordinateBox Mbound j := Fintype.piFinset_subset _ _ hA
  let D : ℝ := diagonalProduct Hbound Mbound j
  let Q : ℝ := (coordinateBox Mbound j).card
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hlabels : ((Fintype.piFinset H).card : ℝ)*((Fintype.piFinset A).card : ℝ) ≤ D := by
    have hc := Nat.mul_le_mul (Finset.card_le_card hHs) (Finset.card_le_card hAs)
    rw [coordinate_card_product] at hc
    dsimp [D]
    exact_mod_cast hc
  have hAC : ((Fintype.piFinset A).card : ℝ) ≤ Q := by
    dsimp [Q]
    exact_mod_cast Finset.card_le_card hAs
  have hvolume : ((Fintype.piFinset H).card : ℝ)*((Fintype.piFinset A).card : ℝ)^2 ≤ D*Q := by
    calc
      _ = (((Fintype.piFinset H).card : ℝ)*((Fintype.piFinset A).card : ℝ))*
        ((Fintype.piFinset A).card : ℝ) := by ring
      _ ≤ _ := mul_le_mul hlabels hAC (Nat.cast_nonneg _) hD
  have hw := hweight P hP k (by omega) H A Hbound Mbound hH hA hsize hparam
  have hb := hsource P hPP H A G
    (by
      intro i h hh
      have he := Finset.mem_Icc.mp (hH i hh)
      exact ⟨by omega,(by exact_mod_cast he.2 : (h : ℝ) ≤ Hbound i.val).trans (hbox i.val i.isLt).1⟩)
    hG
    (by
      intro i m hm
      have he := Finset.mem_Icc.mp (hA i hm)
      exact ⟨by omega,(by exact_mod_cast he.2 : (m : ℝ) ≤ Mbound i.val).trans (hbox i.val i.isLt).2⟩)
    Z hZ
  apply hb.trans
  calc
    _ ≤ ((Fintype.piFinset G).card : ℝ)*
        (C₀*P^(ε/2)*(P*(C₁*P^(ε/2)*D)+D*Q*(C₂*1))) := by
      rw [show C₀*P^(ε/2)*((Fintype.piFinset G).card : ℝ)=
        ((Fintype.piFinset G).card : ℝ)*(C₀*P^(ε/2)) by ring,mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul hZcard hw (Nat.cast_nonneg _) (zero_le_one.trans hP))
        (by simpa only [C₂,mul_one] using hvolume)
    _ = ((Fintype.piFinset G).card : ℝ)*
        (C₀*P^(ε/2)*(C₁*P^(ε/2)*(P*D)+C₂*(D*Q*1))) := by ring
    _ ≤ ((Fintype.piFinset G).card : ℝ)*
        ((C₀*(C₁+C₂))*P^ε*((P*D)+(D*Q*1))) :=
      mul_le_mul_of_nonneg_left (scale_split_bound hP hε hC₀.le hC₁.le hC₂
        (by positivity) (by positivity)) (Nat.cast_nonneg _)
    _ = _ := by dsimp [D,Q]; ring

#print axioms sharp_padded_second_moment_divisor_box
end Waring.PolicyCompletionSharpResidualDivisorBox
