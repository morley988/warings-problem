import WaringSiegel.WSL3LocalWeightedBase

/-! # WSL3: a target-uniform weighted local conductor series, including bad primes -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing Filter Topology
open scoped BigOperators Classical
namespace WaringSiegel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem weightedCubicIncrement_scaling {a b : R} (n : ℕ)
    (he : normalizedLocalCubicCount R 8 (n+4) a - normalizedLocalCubicCount R 8 (n+3) a =
      (1 / (Nat.card (ResidueField R) : ℝ)^5) *
        (normalizedLocalCubicCount R 8 (n+1) b - normalizedLocalCubicCount R 8 n b)) :
    weightedCubicIncrement R a (n+3) =
      (1 / (Nat.card (ResidueField R) : ℝ)^4) * weightedCubicIncrement R b n := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold weightedCubicIncrement
  rw [show n+3+1 = n+4 by omega, cubicConductorWeight_add_three, he,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (Nat.card (ResidueField R) : ℝ)^5)]
  field_simp

theorem weightedCubicIncrement_good_recurrence
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) :
    ∃ b : R, ∀ n : ℕ, 0 ≤ n → weightedCubicIncrement R a (n+3) ≤
      (1 / (Nat.card (ResidueField R) : ℝ)^4) * weightedCubicIncrement R b n := by
  rcases normalized_cubic_increment_three_step (three_isUnit_of_six_residue_ne_zero h6) a with hz | ⟨b,hb⟩
  · refine ⟨a, ?_⟩
    intro n _
    have he : weightedCubicIncrement R a (n+3) = 0 := by
      unfold weightedCubicIncrement
      rw [show n+3+1 = n+4 by omega, hz, abs_zero, mul_zero]
    rw [he]
    exact mul_nonneg (by positivity) (weightedCubicIncrement_nonneg a n)
  · exact ⟨b, fun n _ => (weightedCubicIncrement_scaling n (hb n)).le⟩

theorem weightedCubicIncrement_all_primes_recurrence
    (h3 : (3 : R) ≠ 0) (a : R) :
    ∃ b : R, ∀ n : ℕ, 2*cubicDerivativeOrder R ≤ n →
      weightedCubicIncrement R a (n+3) ≤
        (1 / (Nat.card (ResidueField R) : ℝ)^4) * weightedCubicIncrement R b n := by
  by_cases ha : a ∈ maximalIdeal R^3
  · obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b,rfl⟩ := ha
    refine ⟨b, ?_⟩
    intro n hn
    apply (weightedCubicIncrement_scaling n ?_).le
    rw [show n+4 = (n+1)+3 by omega,
      normalized_cubic_count_scaling_recurrence_all_primes h3 hπ (n+1) (by omega),
      normalized_cubic_count_scaling_recurrence_all_primes h3 hπ n (by omega)]
    ring
  · refine ⟨a, ?_⟩
    intro n hn
    have he : weightedCubicIncrement R a (n+3) = 0 := by
      unfold weightedCubicIncrement
      rw [show n+3+1 = (n+1)+3 by omega,
        normalized_cubic_count_ramified_eq_of_not_mem_cube_ideal h3 (n+1) (by omega) ha,
        normalized_cubic_count_ramified_eq_of_not_mem_cube_ideal h3 n (by omega) ha,
        sub_self, abs_zero, mul_zero]
    rw [he]
    exact mul_nonneg (by positivity) (weightedCubicIncrement_nonneg a n)

theorem cubic_weighted_singular_ratio_le_half :
    1 / (Nat.card (ResidueField R) : ℝ)^4 ≤ (1/2 : ℝ) := by
  have hq2 : 2 ≤ (Nat.card (ResidueField R) : ℝ) := by
    letI := Fintype.ofFinite (ResidueField R)
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (show 2 ≤ Fintype.card (ResidueField R) from Fintype.one_lt_card)
  apply one_div_le_one_div_of_le (by norm_num)
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq2 4
  norm_num at h
  linarith

theorem weightedCubicIncrement_good_summable_bound
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) :
    Summable (weightedCubicIncrement R a) ∧
      (∑' n, weightedCubicIncrement R a n) ≤ 3096 / (Nat.card (ResidueField R) : ℝ)^2 := by
  have h := eventual_three_step_summable_bound (weightedCubicIncrement R) 0
    (516 / (Nat.card (ResidueField R) : ℝ)^2)
    (1 / (Nat.card (ResidueField R) : ℝ)^4) (by positivity) (by positivity)
    cubic_weighted_singular_ratio_le_half weightedCubicIncrement_nonneg
    (by simpa only [zero_add] using weightedCubicIncrement_good_initial h6)
    (weightedCubicIncrement_good_recurrence h6) a
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> norm_num <;> ring

def cubicBadPrimeWeightedMass (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] : ℝ :=
  2*(2*cubicDerivativeOrder R+3 : ℕ) *
    (Nat.card (ResidueField R) : ℝ)^(2*(2*cubicDerivativeOrder R+3))

theorem weightedCubicIncrement_all_primes_summable_bound
    (h3 : (3 : R) ≠ 0) (a : R) :
    Summable (weightedCubicIncrement R a) ∧
      (∑' n, weightedCubicIncrement R a n) ≤ cubicBadPrimeWeightedMass R := by
  exact eventual_three_step_summable_bound (weightedCubicIncrement R) (2*cubicDerivativeOrder R)
    ((Nat.card (ResidueField R) : ℝ)^(2*(2*cubicDerivativeOrder R+3)))
    (1 / (Nat.card (ResidueField R) : ℝ)^4) (by positivity) (by positivity)
    cubic_weighted_singular_ratio_le_half weightedCubicIncrement_nonneg
    (fun a n hn => weightedCubicIncrement_initial_bound _ n hn a)
    (weightedCubicIncrement_all_primes_recurrence h3) a

end WaringSiegel

#print axioms WaringSiegel.weightedCubicIncrement_all_primes_summable_bound
