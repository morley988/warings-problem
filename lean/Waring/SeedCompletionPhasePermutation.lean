import Waring.IntegerDifferencePolynomial
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
namespace Waring.IntegerDifferencePolynomial
open Polynomial

theorem difference_commute (k : ℕ) (h₁ m₁ h₂ m₂ : ℤ) (p : Polynomial ℤ)
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    difference k h₁ m₁ (difference k h₂ m₂ p) =
      difference k h₂ m₂ (difference k h₁ m₁ p) := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) (Int.cast_injective (α := ℝ))
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_map]
  rw [difference_eval_real k h₁ m₁ _ hm₁,difference_eval_real k h₂ m₂ _ hm₂]
  simp only [difference_eval_real k h₁ m₁ _ hm₁,difference_eval_real k h₂ m₂ _ hm₂]
  have hpp : z+(h₁:ℝ)*(m₁:ℝ)^k+(h₂:ℝ)*(m₂:ℝ)^k =
      z+(h₂:ℝ)*(m₂:ℝ)^k+(h₁:ℝ)*(m₁:ℝ)^k := by ring
  have hpm : z+(h₁:ℝ)*(m₁:ℝ)^k-(h₂:ℝ)*(m₂:ℝ)^k =
      z-(h₂:ℝ)*(m₂:ℝ)^k+(h₁:ℝ)*(m₁:ℝ)^k := by ring
  have hmp : z-(h₁:ℝ)*(m₁:ℝ)^k+(h₂:ℝ)*(m₂:ℝ)^k =
      z+(h₂:ℝ)*(m₂:ℝ)^k-(h₁:ℝ)*(m₁:ℝ)^k := by ring
  have hmm : z-(h₁:ℝ)*(m₁:ℝ)^k-(h₂:ℝ)*(m₂:ℝ)^k =
      z-(h₂:ℝ)*(m₂:ℝ)^k-(h₁:ℝ)*(m₁:ℝ)^k := by ring
  rw [hpp,hpm,hmp,hmm]
  ring

theorem powerPolynomial_perm (k : ℕ) {xs ys : List (ℤ × ℤ)} (hperm : xs.Perm ys)
    (hm : ∀ p∈xs,p.2≠0) : powerPolynomial k xs=powerPolynomial k ys := by
  induction hperm with
  | nil => rfl
  | @cons a l₁ l₂ hperm ih =>
    simp only [powerPolynomial]
    rw [ih (fun p hp => hm p (List.mem_cons_of_mem _ hp))]
  | swap a b l =>
    simp only [powerPolynomial]
    exact difference_commute k b.1 b.2 a.1 a.2 (powerPolynomial k l)
      (hm b (by simp)) (hm a (by simp))
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ hm).trans (ih₂ (fun p hp => hm p (h₁.mem_iff.mpr hp)))

#print axioms difference_commute
#print axioms powerPolynomial_perm
end Waring.IntegerDifferencePolynomial
