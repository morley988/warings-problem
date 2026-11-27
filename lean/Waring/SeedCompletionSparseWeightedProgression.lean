import Waring.SeedCompletionSparseWeightedCounts
import Waring.SeedCompletionSparseWeightedSmall

/-! # Exact cancellation of a positive height in a homogeneous sparse moment -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted
open PolicyCompletionHolder SeedCompletionSparseDiagonal

def progressionPhase {J : ℕ} (p q : ℕ) (h m : ℕ) (r : Fin J) : ℤ :=
  (h : ℤ)^(q*(r.val+1)) * (m : ℤ)^(p*(r.val+1))

theorem homogeneous_vectorCollision_eq_progression {J s : ℕ} (p q h : ℕ)
    (hh : 0 < h) (A : Finset ℕ) :
    vectorCollision (fun _ : Fin s => A) (fun _ => progressionPhase (J := J) p q h) =
      progressionSolutions p J s A := by
  classical
  apply Finset.filter_congr
  intro xy hxy
  constructor
  · intro he r
    have hr := congrFun he r
    simp only [vectorFrequency, Finset.sum_apply, progressionPhase, ← Finset.mul_sum] at hr
    have hhZ : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
    have hc := mul_left_cancel₀ (pow_ne_zero (q*(r.val+1)) hhZ) hr
    exact_mod_cast hc
  · intro he
    funext r
    simp only [vectorFrequency, Finset.sum_apply, progressionPhase, ← Finset.mul_sum]
    congr 1
    exact_mod_cast he r

theorem progression_code_moment_eq_card {J s : ℕ} (p q h : ℕ) (hh : 0 < h)
    (A : Finset ℕ) (b : ℤ)
    (hb : ∀ d ∈ constraintVectors (fun _ : Fin s => A)
        (fun _ => progressionPhase (J := J) p q h), code b d=0 ↔ d=0) :
    frequencyEvenMoment A (fun m => code b (progressionPhase (J := J) p q h m)) s =
      ((progressionSolutions p J s A).card : ℝ) := by
  have he := vectorCollision_eq_integral (fun _ : Fin s => A)
    (fun _ => progressionPhase (J := J) p q h) b hb
  rw [homogeneous_vectorCollision_eq_progression p q h hh A] at he
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul,
    frequencyEvenMoment,frequencySum] using he.symm

theorem progression_code_moment_bound (p q J s : ℕ) (hp : 0 < p)
    (hJ : 2 ≤ J) (hs : 1 ≤ s) (hsJ : s ≤ J+1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ A : Finset ℕ,
      (∀ a ∈ A, (a : ℝ) ≤ M) → (A.card : ℝ) ≤ M →
      ∀ h : ℕ, 0 < h → ∀ b : ℤ,
      (∀ d ∈ constraintVectors (fun _ : Fin s => A)
        (fun _ => progressionPhase (J := J) p q h), code b d=0 ↔ d=0) →
      frequencyEvenMoment A (fun m => code b (progressionPhase (J := J) p q h m)) s
        ≤ C*M^((s : ℝ)+δ) := by
  obtain ⟨C,hC,hbound⟩ := progression_solutions_subpower_uniform p J s hp hJ hs hsJ hδ
  refine ⟨C,hC,?_⟩
  intro M hM A hA hcard h hh b hb
  rw [progression_code_moment_eq_card p q h hh A b hb]
  exact hbound M hM A hA hcard

#print axioms progression_code_moment_eq_card
#print axioms progression_code_moment_bound
end Waring.SeedCompletionSparseWeighted
