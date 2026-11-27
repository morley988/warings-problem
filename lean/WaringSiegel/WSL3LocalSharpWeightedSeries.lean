import WaringSiegel.WSL3LocalSharpWeightedBase

/-! # WSL3: all-prime local summability with conductor exponent 5/4 -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing Filter Topology
open scoped BigOperators Classical
namespace WaringSiegel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem sharpWeightedCubicIncrement_scaling {a b : R} (n : ℕ)
    (he : normalizedLocalCubicCount R 8 (n+4) a - normalizedLocalCubicCount R 8 (n+3) a =
      (1 / (Nat.card (ResidueField R) : ℝ)^5) *
        (normalizedLocalCubicCount R 8 (n+1) b - normalizedLocalCubicCount R 8 n b)) :
    sharpWeightedCubicIncrement R a (n+3) =
      (1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ)) * sharpWeightedCubicIncrement R b n := by
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hw : sharpCubicConductorWeight R (n+3) * (1 / (Nat.card (ResidueField R) : ℝ)^5) =
      (1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ)) * sharpCubicConductorWeight R n := by
    unfold sharpCubicConductorWeight
    rw [one_div, ← Real.rpow_natCast (Nat.card (ResidueField R) : ℝ) 5,
      ← Real.rpow_neg hq.le, ← Real.rpow_add hq,
      one_div, ← Real.rpow_neg hq.le, ← Real.rpow_add hq]
    congr 1
    push_cast
    ring
  unfold sharpWeightedCubicIncrement
  rw [show n+3+1 = n+4 by omega, he, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (Nat.card (ResidueField R) : ℝ)^5),
    ← mul_assoc, hw, mul_assoc]

theorem sharpWeightedCubicIncrement_good_recurrence
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) :
    ∃ b : R, ∀ n : ℕ, 0 ≤ n → sharpWeightedCubicIncrement R a (n+3) ≤
      (1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ)) * sharpWeightedCubicIncrement R b n := by
  rcases normalized_cubic_increment_three_step (three_isUnit_of_six_residue_ne_zero h6) a with hz | ⟨b,hb⟩
  · refine ⟨a, ?_⟩
    intro n _
    have he : sharpWeightedCubicIncrement R a (n+3) = 0 := by
      unfold sharpWeightedCubicIncrement
      rw [show n+3+1 = n+4 by omega, hz, abs_zero, mul_zero]
    rw [he]
    exact mul_nonneg (by positivity) (sharpWeightedCubicIncrement_nonneg a n)
  · exact ⟨b, fun n _ => (sharpWeightedCubicIncrement_scaling n (hb n)).le⟩

theorem sharpWeightedCubicIncrement_all_primes_recurrence
    (h3 : (3 : R) ≠ 0) (a : R) :
    ∃ b : R, ∀ n : ℕ, 2*cubicDerivativeOrder R ≤ n →
      sharpWeightedCubicIncrement R a (n+3) ≤
        (1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ)) * sharpWeightedCubicIncrement R b n := by
  by_cases ha : a ∈ maximalIdeal R^3
  · obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b,rfl⟩ := ha
    refine ⟨b, ?_⟩
    intro n hn
    apply (sharpWeightedCubicIncrement_scaling n ?_).le
    rw [show n+4 = (n+1)+3 by omega,
      normalized_cubic_count_scaling_recurrence_all_primes h3 hπ (n+1) (by omega),
      normalized_cubic_count_scaling_recurrence_all_primes h3 hπ n (by omega)]
    ring
  · refine ⟨a, ?_⟩
    intro n hn
    have he : sharpWeightedCubicIncrement R a (n+3) = 0 := by
      unfold sharpWeightedCubicIncrement
      rw [show n+3+1 = (n+1)+3 by omega,
        normalized_cubic_count_ramified_eq_of_not_mem_cube_ideal h3 (n+1) (by omega) ha,
        normalized_cubic_count_ramified_eq_of_not_mem_cube_ideal h3 n (by omega) ha,
        sub_self, abs_zero, mul_zero]
    rw [he]
    exact mul_nonneg (by positivity) (sharpWeightedCubicIncrement_nonneg a n)

theorem cubic_sharp_weighted_ratio_le_half :
    1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ) ≤ (1/2 : ℝ) := by
  have hq2 : 2 ≤ (Nat.card (ResidueField R) : ℝ) := by
    letI := Fintype.ofFinite (ResidueField R)
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (show 2 ≤ Fintype.card (ResidueField R) from Fintype.one_lt_card)
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := by linarith
  apply one_div_le_one_div_of_le (by norm_num)
  exact hq2.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 : ℝ) ≤ 5/4))

theorem sharpWeightedCubicIncrement_good_summable_bound
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) :
    Summable (sharpWeightedCubicIncrement R a) ∧
      (∑' n, sharpWeightedCubicIncrement R a n) ≤
        1548 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ) := by
  have h := eventual_three_step_summable_bound (sharpWeightedCubicIncrement R) 0
    (258 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ))
    (1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ)) (by positivity) (by positivity)
    cubic_sharp_weighted_ratio_le_half sharpWeightedCubicIncrement_nonneg
    (by simpa only [zero_add] using sharpWeightedCubicIncrement_good_initial h6)
    (sharpWeightedCubicIncrement_good_recurrence h6) a
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> norm_num <;> ring

theorem sharpWeightedCubicIncrement_initial_bound (T n : ℕ) (hn : n < T+3) (a : R) :
    sharpWeightedCubicIncrement R a n ≤ (Nat.card (ResidueField R) : ℝ)^(3*(T+3)) := by
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  have h₀ := normalizedLocalCubicCount_nonneg a n
  have h₁ := normalizedLocalCubicCount_nonneg a (n+1)
  have hnupper := (normalizedLocalCubicCount_le_residue_pow a n).trans
    (pow_le_pow_right₀ hq1 (by omega : n ≤ T+3))
  have hsuccupper := (normalizedLocalCubicCount_le_residue_pow a (n+1)).trans
    (pow_le_pow_right₀ hq1 (by omega : n+1 ≤ T+3))
  have habs : |normalizedLocalCubicCount R 8 (n+1) a - normalizedLocalCubicCount R 8 n a| ≤
      (Nat.card (ResidueField R) : ℝ)^(T+3) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hw : sharpCubicConductorWeight R n ≤ (Nat.card (ResidueField R) : ℝ)^(2*(T+3)) := by
    unfold sharpCubicConductorWeight
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    have hn' : (n : ℝ)+1 ≤ (T : ℝ)+3 := by exact_mod_cast hn
    push_cast
    nlinarith
  unfold sharpWeightedCubicIncrement
  calc
    _ ≤ (Nat.card (ResidueField R) : ℝ)^(2*(T+3)) *
        (Nat.card (ResidueField R) : ℝ)^(T+3) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

def cubicBadPrimeSharpWeightedMass (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] : ℝ :=
  2*(2*cubicDerivativeOrder R+3 : ℕ) *
    (Nat.card (ResidueField R) : ℝ)^(3*(2*cubicDerivativeOrder R+3))

theorem sharpWeightedCubicIncrement_all_primes_summable_bound
    (h3 : (3 : R) ≠ 0) (a : R) :
    Summable (sharpWeightedCubicIncrement R a) ∧
      (∑' n, sharpWeightedCubicIncrement R a n) ≤ cubicBadPrimeSharpWeightedMass R := by
  exact eventual_three_step_summable_bound (sharpWeightedCubicIncrement R) (2*cubicDerivativeOrder R)
    ((Nat.card (ResidueField R) : ℝ)^(3*(2*cubicDerivativeOrder R+3)))
    (1 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ)) (by positivity) (by positivity)
    cubic_sharp_weighted_ratio_le_half sharpWeightedCubicIncrement_nonneg
    (fun a n hn => sharpWeightedCubicIncrement_initial_bound _ n hn a)
    (sharpWeightedCubicIncrement_all_primes_recurrence h3) a

end WaringSiegel
#print axioms WaringSiegel.sharpWeightedCubicIncrement_all_primes_summable_bound
