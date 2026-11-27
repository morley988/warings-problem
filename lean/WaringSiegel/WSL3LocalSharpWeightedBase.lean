import WaringSiegel.WSL3LocalWeightedSeries

/-! # WSL3: sharp initial conductor increments and the 5/4 weight -/
noncomputable section
set_option maxHeartbeats 100000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel

lemma rpow_mul_div_nat_pow_le {q c a t : ℝ} (hq : 1 ≤ q) (hc : 0 ≤ c)
    (b : ℕ) (hab : a - (b : ℝ) ≤ -t) :
    q^a * (c / q^b) ≤ c / q^t := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ = c * q^(a-(b : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_neg hq0.le,
        Real.rpow_natCast]
      ring
    _ ≤ c * q^(-t) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq hab) hc
    _ = _ := by rw [Real.rpow_neg hq0.le]; ring

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

def sharpCubicConductorWeight (R : Type*) [CommRing R] [IsLocalRing R] (n : ℕ) : ℝ :=
  (Nat.card (ResidueField R) : ℝ)^((5/4 : ℝ)*(n+1))

def sharpWeightedCubicIncrement (R : Type*) [CommRing R] [IsLocalRing R] (a : R) (n : ℕ) : ℝ :=
  sharpCubicConductorWeight R n *
    |normalizedLocalCubicCount R 8 (n+1) a - normalizedLocalCubicCount R 8 n a|

theorem sharpWeightedCubicIncrement_nonneg (a : R) (n : ℕ) :
    0 ≤ sharpWeightedCubicIncrement R a n := by
  unfold sharpWeightedCubicIncrement sharpCubicConductorWeight
  positivity

theorem normalized_cubic_increment_two_sharp (h3 : IsUnit (3 : R)) (a : R) :
    |normalizedLocalCubicCount R 8 2 a - normalizedLocalCubicCount R 8 1 a| ≤
      1 / (Nat.card (ResidueField R) : ℝ)^6 := by
  have hq0 : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  obtain ⟨h10,h1⟩ := normalized_cubic_count_sub_primitive_bounds h3 0 a
  obtain ⟨h20,h2⟩ := normalized_cubic_count_sub_primitive_bounds h3 1 a
  norm_num only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.mul_one, pow_zero,
    Nat.reduceAdd, Nat.reduceMul] at h10 h1 h20 h2
  have he : (Nat.card (ResidueField R) : ℝ)^8 / (Nat.card (ResidueField R) : ℝ)^14 =
      1 / (Nat.card (ResidueField R) : ℝ)^6 := by field_simp
  rw [he] at h2
  have h76 : 1 / (Nat.card (ResidueField R) : ℝ)^7 ≤
      1 / (Nat.card (ResidueField R) : ℝ)^6 :=
    one_div_le_one_div_of_le (pow_pos (by positivity) 6)
      (pow_le_pow_right₀ hq1 (by decide))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem normalized_cubic_increment_three_sharp (h3 : IsUnit (3 : R)) (a : R) :
    |normalizedLocalCubicCount R 8 3 a - normalizedLocalCubicCount R 8 2 a| ≤
      1 / (Nat.card (ResidueField R) : ℝ)^5 := by
  have hq0 : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  obtain ⟨h20,h2⟩ := normalized_cubic_count_sub_primitive_bounds h3 1 a
  obtain ⟨h30,h3'⟩ := normalized_cubic_count_sub_primitive_bounds h3 2 a
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at h20 h2 h30 h3'
  have he2 : (Nat.card (ResidueField R) : ℝ)^8 / (Nat.card (ResidueField R) : ℝ)^14 =
      1 / (Nat.card (ResidueField R) : ℝ)^6 := by field_simp
  have he3 : (Nat.card (ResidueField R) : ℝ)^16 / (Nat.card (ResidueField R) : ℝ)^21 =
      1 / (Nat.card (ResidueField R) : ℝ)^5 := by field_simp
  rw [he2] at h2
  rw [he3] at h3'
  have h65 : 1 / (Nat.card (ResidueField R) : ℝ)^6 ≤
      1 / (Nat.card (ResidueField R) : ℝ)^5 :=
    one_div_le_one_div_of_le (pow_pos (by positivity) 5)
      (pow_le_pow_right₀ hq1 (by decide))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem sharpWeightedCubicIncrement_good_initial
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) (n : ℕ) (hn : n < 3) :
    sharpWeightedCubicIncrement R a n ≤
      258 / (Nat.card (ResidueField R) : ℝ)^(5/4 : ℝ) := by
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  have h3 := three_isUnit_of_six_residue_ne_zero h6
  unfold sharpWeightedCubicIncrement sharpCubicConductorWeight
  interval_cases n
  · have h := normalized_cubic_count_initial_error h6 0 (by omega) a
    rw [normalizedLocalCubicCount_zero]
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans
      (rpow_mul_div_nat_pow_le hq1 (by norm_num) 3 (by norm_num))
  · have h := normalized_cubic_increment_two_sharp h3 a
    have hc : 1 / (Nat.card (ResidueField R) : ℝ)^6 ≤
        258 / (Nat.card (ResidueField R) : ℝ)^6 :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity)).trans
      (rpow_mul_div_nat_pow_le hq1 (by norm_num) 6 (by norm_num))
  · have h := normalized_cubic_increment_three_sharp h3 a
    have hc : 1 / (Nat.card (ResidueField R) : ℝ)^5 ≤
        258 / (Nat.card (ResidueField R) : ℝ)^5 :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity)).trans
      (rpow_mul_div_nat_pow_le hq1 (by norm_num) 5 (by norm_num))

end WaringSiegel
#print axioms WaringSiegel.sharpWeightedCubicIncrement_good_initial
