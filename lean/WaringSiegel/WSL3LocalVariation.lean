import WaringSiegel.WSL3LocalVariationBase

/-! # WSL3: uniform absolute control of the local conductor series -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel

/-- A contractive three-step recursion bounds total variation uniformly,
even when the target changes in the recursive branch. -/
theorem three_step_variation_bound {A : Type*} (f : A → ℕ → ℝ)
    (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hbase : ∀ a n, n < 3 → |f a (n+1) - f a n| ≤ C)
    (hrec : ∀ a, (∀ n, f a (n+4) - f a (n+3) = 0) ∨
      ∃ b, ∀ n, f a (n+4) - f a (n+3) = r * (f b (n+1) - f b n)) :
    ∀ N a, (∑ n ∈ Finset.range N, |f a (n+1) - f a n|) ≤ 6*C := by
  have hfirst (a : A) (N : ℕ) (hN : N ≤ 3) :
      (∑ n ∈ Finset.range N, |f a (n+1) - f a n|) ≤ 3*C := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, C := by
        apply Finset.sum_le_sum
        intro n hn
        exact hbase a n (lt_of_lt_of_le (Finset.mem_range.mp hn) hN)
      _ = (N : ℝ)*C := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 3*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hC
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a
    by_cases hN : N ≤ 3
    · exact (hfirst a N hN).trans (by nlinarith)
    · have hN3 : 3 < N := Nat.lt_of_not_ge hN
      have he : N = 3 + (N-3) := by omega
      conv_lhs => rw [he, Finset.sum_range_add]
      have hstart := hfirst a 3 le_rfl
      rcases hrec a with hz | ⟨b, hb⟩
      · have htail : (∑ n ∈ Finset.range (N-3),
            |f a (3+n+1) - f a (3+n)|) = 0 := by
          apply Finset.sum_eq_zero
          intro n _
          have he1 : 3+n+1 = n+4 := by omega
          have he2 : 3+n = n+3 := by omega
          rw [he1, he2, hz, abs_zero]
        rw [htail, add_zero]
        exact hstart.trans (by nlinarith)
      · have htail : (∑ n ∈ Finset.range (N-3),
            |f a (3+n+1) - f a (3+n)|) =
            r * ∑ n ∈ Finset.range (N-3), |f b (n+1) - f b n| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          have he1 : 3+n+1 = n+4 := by omega
          have he2 : 3+n = n+3 := by omega
          rw [he1, he2, hb, abs_mul, abs_of_nonneg hr]
        rw [htail]
        have htailbound := mul_le_mul_of_nonneg_left (ih (N-3) (by omega) b) hr
        have hcontract := mul_le_mul_of_nonneg_right hrhalf (show 0 ≤ 6*C by positivity)
        nlinarith

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

@[simp] theorem normalizedLocalCubicCount_zero (a : R) :
    normalizedLocalCubicCount R 8 0 a = 1 := by
  simp only [normalizedLocalCubicCount, pow_zero, Ideal.one_eq_top,
    localCubicSolutionCount_top, Nat.cast_one, mul_zero, div_one]

theorem normalized_cubic_increment_initial
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) (n : ℕ) (hn : n < 3) :
    |normalizedLocalCubicCount R 8 (n+1) a - normalizedLocalCubicCount R 8 n a| ≤
      516 / (Nat.card (ResidueField R) : ℝ)^3 := by
  by_cases hn0 : n = 0
  · subst n
    rw [normalizedLocalCubicCount_zero]
    exact (normalized_cubic_count_initial_error h6 0 (by omega) a).trans (by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity))
  · have he : n = (n-1)+1 := by omega
    have h₁ := normalized_cubic_count_initial_error h6 n (by omega) a
    have h₂ := normalized_cubic_count_initial_error h6 (n-1) (by omega) a
    rw [← he] at h₂
    calc
      _ ≤ |normalizedLocalCubicCount R 8 (n+1) a - 1| +
          |normalizedLocalCubicCount R 8 n a - 1| := by
        simpa only [abs_sub_comm (1 : ℝ) (normalizedLocalCubicCount R 8 n a)] using
          abs_sub_le (normalizedLocalCubicCount R 8 (n+1) a) 1 (normalizedLocalCubicCount R 8 n a)
      _ ≤ 258 / (Nat.card (ResidueField R) : ℝ)^3 +
          258 / (Nat.card (ResidueField R) : ℝ)^3 := add_le_add h₁ h₂
      _ = _ := by ring

theorem normalized_cubic_increment_three_step
    (h3 : IsUnit (3 : R)) (a : R) :
    (∀ n, normalizedLocalCubicCount R 8 (n+4) a -
      normalizedLocalCubicCount R 8 (n+3) a = 0) ∨
    ∃ b : R, ∀ n, normalizedLocalCubicCount R 8 (n+4) a -
      normalizedLocalCubicCount R 8 (n+3) a =
        (1 / (Nat.card (ResidueField R) : ℝ)^5) *
          (normalizedLocalCubicCount R 8 (n+1) b - normalizedLocalCubicCount R 8 n b) := by
  by_cases ha : a ∈ maximalIdeal R^3
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    refine Or.inr ⟨b, ?_⟩
    intro n
    rw [show n+4 = (n+1)+3 by omega,
      normalized_cubic_count_scaling_recurrence h3 hπ (n+1),
      normalized_cubic_count_scaling_recurrence h3 hπ n]
    ring
  · left
    intro n
    rw [show n+4 = (n+1)+3 by omega,
      normalized_cubic_count_eq_of_not_mem_cube_ideal h3 (n+1) ha,
      normalized_cubic_count_eq_of_not_mem_cube_ideal h3 n ha, sub_self]

theorem normalized_cubic_total_variation_bound
    (h6 : (6 : ResidueField R) ≠ 0) (N : ℕ) (a : R) :
    (∑ n ∈ Finset.range N, |normalizedLocalCubicCount R 8 (n+1) a -
      normalizedLocalCubicCount R 8 n a|) ≤ 3096 / (Nat.card (ResidueField R) : ℝ)^3 := by
  have hq0 : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hq2 : 2 ≤ (Nat.card (ResidueField R) : ℝ) := by
    letI := Fintype.ofFinite (ResidueField R)
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (show 2 ≤ Fintype.card (ResidueField R) from Fintype.one_lt_card)
  have hq5 : 2 ≤ (Nat.card (ResidueField R) : ℝ)^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq2 5
    norm_num at h
    linarith
  have hhalf : 1 / (Nat.card (ResidueField R) : ℝ)^5 ≤ (1/2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hq5
  have h := three_step_variation_bound
    (fun a n => normalizedLocalCubicCount R 8 n a)
    (516 / (Nat.card (ResidueField R) : ℝ)^3)
    (1 / (Nat.card (ResidueField R) : ℝ)^5) (by positivity) (by positivity) hhalf
    (normalized_cubic_increment_initial h6)
    (normalized_cubic_increment_three_step (three_isUnit_of_six_residue_ne_zero h6)) N a
  convert h using 1 <;> ring

end WaringSiegel

#print axioms WaringSiegel.normalized_cubic_total_variation_bound
