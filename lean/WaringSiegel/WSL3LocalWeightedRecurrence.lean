import WaringSiegel.WSL3LocalVariation

/-! # WSL3: uniform summation for an eventually contractive local recurrence -/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace WaringSiegel

theorem eventual_three_step_sum_bound {A : Type*} (g : A → ℕ → ℝ)
    (T : ℕ) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hg : ∀ a n, 0 ≤ g a n)
    (hbase : ∀ a n, n < T+3 → g a n ≤ C)
    (hrec : ∀ a, ∃ b, ∀ n, T ≤ n → g a (n+3) ≤ r*g b n) :
    ∀ N a, (∑ n ∈ Finset.range N, g a n) ≤ 2*(T+3 : ℕ)*C := by
  have hfirst (a : A) (N : ℕ) (hN : N ≤ T+3) :
      (∑ n ∈ Finset.range N, g a n) ≤ (T+3 : ℕ)*C := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, C :=
        Finset.sum_le_sum (fun n hn => hbase a n
          (lt_of_lt_of_le (Finset.mem_range.mp hn) hN))
      _ = (N : ℝ)*C := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (T+3 : ℕ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hC
  have hTC : 0 ≤ (T+3 : ℕ)*C := mul_nonneg (Nat.cast_nonneg _) hC
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a
    by_cases hN : N ≤ T+3
    · exact (hfirst a N hN).trans (by nlinarith)
    · have hN' : T+3 < N := Nat.lt_of_not_ge hN
      let L := N-(T+3)
      have hNL : N = (T+3)+L := by dsimp [L]; omega
      have hL : T+L = N-3 := by dsimp [L]; omega
      obtain ⟨b, hb⟩ := hrec a
      have htail : (∑ n ∈ Finset.range L, g a (T+3+n)) ≤
          r * ∑ n ∈ Finset.range (N-3), g b n := by
        calc
          _ ≤ ∑ n ∈ Finset.range L, r*g b (T+n) := by
            apply Finset.sum_le_sum
            intro n _
            simpa only [Nat.add_assoc, Nat.add_comm 3 n] using hb (T+n) (by omega)
          _ = r * ∑ n ∈ Finset.range L, g b (T+n) := (Finset.mul_sum _ _ _).symm
          _ ≤ r * ∑ n ∈ Finset.range (T+L), g b n := by
            apply mul_le_mul_of_nonneg_left _ hr
            rw [Finset.sum_range_add]
            exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => hg b n))
          _ = _ := by rw [hL]
      have hsmall := ih (N-3) (by omega) b
      have hmul := mul_le_mul_of_nonneg_left hsmall hr
      have hcontract := mul_le_mul_of_nonneg_right hrhalf (show 0 ≤ 2*(T+3 : ℕ)*C by positivity)
      have hstart := hfirst a (T+3) le_rfl
      conv_lhs => rw [hNL, Finset.sum_range_add]
      nlinarith

theorem eventual_three_step_summable_bound {A : Type*} (g : A → ℕ → ℝ)
    (T : ℕ) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hg : ∀ a n, 0 ≤ g a n)
    (hbase : ∀ a n, n < T+3 → g a n ≤ C)
    (hrec : ∀ a, ∃ b, ∀ n, T ≤ n → g a (n+3) ≤ r*g b n) (a : A) :
    Summable (g a) ∧ (∑' n, g a n) ≤ 2*(T+3 : ℕ)*C := by
  have hb := fun N => eventual_three_step_sum_bound g T C r hC hr hrhalf hg hbase hrec N a
  have hs := summable_of_sum_range_le (hg a) hb
  exact ⟨hs, le_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hb)⟩

end WaringSiegel
