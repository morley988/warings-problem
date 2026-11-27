import Waring.DivisorBound
import Mathlib.Data.Finset.Prod

/-!
# Positive factor pairs below a cutoff

Grouping actual pairs (d,y) by n=d*y bounds their total by a divisor sum.
This supplies the uniform short-factor coefficient bound in the bad branch
of efficient differencing without assuming a divisor-sum asymptotic.
-/

noncomputable section
open scoped BigOperators
namespace Waring.ProductPairCount

def factorPairs (M N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter (fun p => p.1*p.2 ≤ N)

def shortFactors (M N y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun d => d*y ≤ N)

theorem factorPairs_card_eq_sum (M N : ℕ) :
    (factorPairs M N).card = ∑ y ∈ Finset.Icc 1 N, (shortFactors M N y).card := by
  classical
  have hm : (factorPairs M N).toSet.MapsTo Prod.snd (Finset.Icc 1 N) := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro y hy
  have heq : (factorPairs M N).filter (fun p => p.2=y) =
      (shortFactors M N y).image (fun d => (d,y)) := by
    ext p
    simp only [factorPairs,shortFactors,Finset.mem_filter,Finset.mem_product,Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hd,hy'⟩,hprod⟩,hpy⟩
      subst y
      exact ⟨p.1,⟨hd,hprod⟩,rfl⟩
    · rintro ⟨d,⟨hd,hprod⟩,rfl⟩
      exact ⟨⟨⟨hd,hy⟩,hprod⟩,rfl⟩
  rw [heq,Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]

theorem factorPairs_card_le_divisor_sum (M N : ℕ) :
    (factorPairs M N).card ≤ ∑ n ∈ Finset.Icc 1 N, n.divisors.card := by
  classical
  have hm : (factorPairs M N).toSet.MapsTo (fun p => p.1*p.2) (Finset.Icc 1 N) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hd,hy⟩
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hy).1,hprod⟩
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_le_sum
  intro n hn
  have hsub : (factorPairs M N).filter (fun p => p.1*p.2=n) ⊆ n.divisorsAntidiagonal := by
    intro p hp
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2,
      (by have := (Finset.mem_Icc.mp hn).1; omega)⟩
  have hcard := Finset.card_le_card hsub
  rwa [← Nat.map_div_right_divisors,Finset.card_map] at hcard

theorem factorPairs_card_le_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ M : ℕ,
      ((factorPairs M ⌊Q⌋₊).card : ℝ) ≤ C*Q*Q^ε := by
  obtain ⟨C,hC,hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hε
  refine ⟨C,hC,?_⟩
  intro Q hQ M
  have hcount : ((factorPairs M ⌊Q⌋₊).card : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (n.divisors.card : ℝ) := by
    exact_mod_cast factorPairs_card_le_divisor_sum M ⌊Q⌋₊
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (n.divisors.card : ℝ) := hcount
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊Q⌋₊, C*Q^ε := by
      apply Finset.sum_le_sum
      intro n hn
      rcases Finset.mem_Icc.mp hn with ⟨hnpos,hnQ⟩
      exact hdiv Q hQ n hnpos ((by exact_mod_cast hnQ : (n : ℝ) ≤ (⌊Q⌋₊ : ℝ)).trans
        (Nat.floor_le (zero_le_one.trans hQ)))
    _ = (⌊Q⌋₊ : ℝ)*(C*Q^ε) := by simp
    _ ≤ Q*(C*Q^ε) := mul_le_mul_of_nonneg_right
      (Nat.floor_le (zero_le_one.trans hQ)) (by positivity)
    _ = C*Q*Q^ε := by ring

#print axioms factorPairs_card_le_divisor_sum
#print axioms factorPairs_card_le_cutoff
end Waring.ProductPairCount
