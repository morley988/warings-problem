import WaringSiegel.WSL3LocalWeightedRecurrence

/-! # WSL3: weighted conductor increments at every finite prime -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

def cubicConductorWeight (R : Type*) [CommRing R] [IsLocalRing R] (n : ℕ) : ℝ :=
  (Nat.card (ResidueField R) : ℝ)^(n/3+1)

def weightedCubicIncrement (R : Type*) [CommRing R] [IsLocalRing R] (a : R) (n : ℕ) : ℝ :=
  cubicConductorWeight R n *
    |normalizedLocalCubicCount R 8 (n+1) a - normalizedLocalCubicCount R 8 n a|

theorem weightedCubicIncrement_nonneg (a : R) (n : ℕ) :
    0 ≤ weightedCubicIncrement R a n := by
  unfold weightedCubicIncrement cubicConductorWeight
  positivity

theorem normalizedLocalCubicCount_nonneg (a : R) (n : ℕ) :
    0 ≤ normalizedLocalCubicCount R 8 n a := by
  unfold normalizedLocalCubicCount
  positivity

/-- Dropping the congruence equation gives a uniform bound at every precision. -/
theorem normalizedLocalCubicCount_le_residue_pow (a : R) (n : ℕ) :
    normalizedLocalCubicCount R 8 n a ≤ (Nat.card (ResidueField R) : ℝ)^n := by
  letI := dvr_power_quotient_finite (R := R) n
  have hc := Nat.card_le_card_of_injective
    (fun x : LocalCubicSolutions R (maximalIdeal R^n) 8 a => x.val) Subtype.val_injective
  have hc' : localCubicSolutionCount R (maximalIdeal R^n) 8 a ≤
      Nat.card (ResidueField R)^(8*n) := by
    simpa only [localCubicSolutionCount, Nat.card_fun, Nat.card_fin,
      dvr_power_quotient_card, ← pow_mul, Nat.mul_comm n 8] using hc
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  unfold normalizedLocalCubicCount
  norm_num only
  apply (div_le_iff₀ (pow_pos hq _)).mpr
  rw [← pow_add, show n+7*n = 8*n by omega]
  exact_mod_cast hc'

theorem weightedCubicIncrement_initial_bound (T n : ℕ) (hn : n < T+3) (a : R) :
    weightedCubicIncrement R a n ≤ (Nat.card (ResidueField R) : ℝ)^(2*(T+3)) := by
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  have h₀ := normalizedLocalCubicCount_nonneg a n
  have h₁ := normalizedLocalCubicCount_nonneg a (n+1)
  have hnupper := (normalizedLocalCubicCount_le_residue_pow a n).trans
    (pow_le_pow_right₀ hq1 (by omega : n ≤ T+3))
  have hsuccupper := (normalizedLocalCubicCount_le_residue_pow a (n+1)).trans
    (pow_le_pow_right₀ hq1 (by omega : n+1 ≤ T+3))
  have habs : |normalizedLocalCubicCount R 8 (n+1) a - normalizedLocalCubicCount R 8 n a| ≤
      (Nat.card (ResidueField R) : ℝ)^(T+3) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hw : cubicConductorWeight R n ≤ (Nat.card (ResidueField R) : ℝ)^(T+3) := by
    apply pow_le_pow_right₀ hq1
    have hd := Nat.div_le_self n 3
    omega
  unfold weightedCubicIncrement
  calc
    _ ≤ (Nat.card (ResidueField R) : ℝ)^(T+3) *
        (Nat.card (ResidueField R) : ℝ)^(T+3) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem cubicConductorWeight_add_three (n : ℕ) :
    cubicConductorWeight R (n+3) =
      (Nat.card (ResidueField R) : ℝ) * cubicConductorWeight R n := by
  unfold cubicConductorWeight
  have hdiv : (n+3)/3 = n/3+1 := by omega
  rw [hdiv, pow_succ]
  ring

theorem weightedCubicIncrement_good_initial
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) (n : ℕ) (hn : n < 3) :
    weightedCubicIncrement R a n ≤ 516 / (Nat.card (ResidueField R) : ℝ)^2 := by
  have hq0 : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hw : cubicConductorWeight R n = (Nat.card (ResidueField R) : ℝ) := by
    simp only [cubicConductorWeight, Nat.div_eq_of_lt hn, zero_add, pow_one]
  unfold weightedCubicIncrement
  rw [hw]
  calc
    _ ≤ (Nat.card (ResidueField R) : ℝ) *
        (516 / (Nat.card (ResidueField R) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left (normalized_cubic_increment_initial h6 a n hn) hq0.le
    _ = _ := by field_simp

end WaringSiegel
