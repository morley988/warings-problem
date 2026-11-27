import Waring.SeedCompletionSparseWeightedHolder
import Waring.SeedCompletionSparseWeightedProgression

/-!
# The actual weighted sparse diagonal estimate

The height tuples are common to both sides. They are not replaced by
independent coefficient-height choices. Exact vector orthogonality,
finite Jensen, and normalized Holder give the required product of the
height and coefficient lengths.
-/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted

theorem weighted_progression_subpower (p q J s : ℕ) (hp : 0 < p)
    (hJ : 2 ≤ J) (hs : 1 ≤ s) (hsJ : s ≤ J+1) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ H A : Fin s → Finset ℕ, ∀ Hcap M : Fin s → ℝ,
      (∀ i, 0 < Hcap i) → (∀ i, (H i).card ≤ Hcap i) →
      (∀ i, ∀ h ∈ H i, 0 < h) →
      (∀ i, 1 ≤ M i) → (∀ i, M i ≤ P^B) →
      (∀ i, ∀ m ∈ A i, (m : ℝ) ≤ M i) → (∀ i, (A i).card ≤ M i) →
      (weightedCount H A (fun _ => progressionPhase (J := J) p q) : ℝ)
        ≤ C * P^ε * ∏ i, (Hcap i * M i) := by
  let δ := ε/(B+1)
  have hden : 0 < B+1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C,hC,hbound⟩ := progression_code_moment_bound p q J s hp hJ hs hsJ hδ
  refine ⟨C,hC,?_⟩
  intro P hP H A Hcap M hHpos hHcard hHpositive hM hMP hA hAcard
  obtain ⟨b,hbm,hbh⟩ := exists_joint_code H A
    (fun _ => progressionPhase (J := J) p q)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hMpos (i : Fin s) : 0 < M i := zero_lt_one.trans_le (hM i)
  apply weightedCount_le_of_moments (by omega) H A
    (fun _ => progressionPhase (J := J) p q) b Hcap M hHcard hHpos hMpos
    (C*P^ε) (by positivity) hbm
  intro i h hh
  apply (hbound (M i) (hM i) (A i) (hA i) (hAcard i) h
    (hHpositive i h hh) b (hbh i h hh)).trans
  have hδB : B*δ ≤ ε := by
    have hδeq : (B+1)*δ=ε := by dsimp [δ]; field_simp
    nlinarith
  have hsmall : (M i)^δ ≤ P^ε := by
    calc
      _ ≤ (P^B)^δ := Real.rpow_le_rpow (hMpos i).le (hMP i) hδ.le
      _ = P^(B*δ) := (Real.rpow_mul hPpos.le B δ).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hδB
  calc
    _ = C*((M i)^s * (M i)^δ) := by
      rw [Real.rpow_add (hMpos i),Real.rpow_natCast]
    _ ≤ C*((M i)^s * P^ε) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsmall (pow_nonneg (hMpos i).le s)) hC.le
    _ = _ := by ring

theorem weighted_even_progression_subpower (k J s : ℕ) (hk : 1 ≤ k)
    (hJ : 2 ≤ J) (hs : 1 ≤ s) (hsJ : s ≤ J+1) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ H A : Fin s → Finset ℕ, ∀ Hcap M : Fin s → ℝ,
      (∀ i, 0 < Hcap i) → (∀ i, (H i).card ≤ Hcap i) →
      (∀ i, ∀ h ∈ H i, 0 < h) →
      (∀ i, 1 ≤ M i) → (∀ i, M i ≤ P^B) →
      (∀ i, ∀ m ∈ A i, (m : ℝ) ≤ M i) → (∀ i, (A i).card ≤ M i) →
      (weightedCount H A (fun _ => progressionPhase (J := J) (2*k) 2) : ℝ)
        ≤ C * P^ε * ∏ i, (Hcap i * M i) :=
  weighted_progression_subpower (2*k) 2 J s (by omega) hJ hs hsJ hB hε

#print axioms weighted_progression_subpower
#print axioms weighted_even_progression_subpower
end Waring.SeedCompletionSparseWeighted
