import WaringSiegel.WSL2LocalSingular

/-!
# Cubic local-density convergence away from 3

The exact primitive count and the uniformizer scaling recurrence yield
stabilization for nonzero targets, including targets divisible by the prime.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped BigOperators

namespace WaringSiegel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

def primitiveEightCubicDensity (R : Type*) [CommRing R] [IsLocalRing R] (a : R) : ℝ :=
  (Nat.card (PrimitiveCubicResidues R 8 a) : ℝ) /
    (Nat.card (ResidueField R) : ℝ) ^ 7

theorem normalized_cubic_count_eq_of_not_mem_cube_ideal
    (h3 : IsUnit (3 : R)) (n : ℕ) {a : R} (ha : a ∉ maximalIdeal R ^ 3) :
    normalizedLocalCubicCount R 8 (n + 3) a = primitiveEightCubicDensity R a := by
  letI := dvr_power_quotient_finite (R := R) (n + 3)
  have hc := local_cubic_count_primitive_add_singular (maximalIdeal R ^ (n + 3))
    (Ideal.pow_le_self (by omega)) 8 a
  rw [singular_local_cubic_count_zero n 8 ha, add_zero] at hc
  have he : normalizedLocalCubicCount R 8 (n + 3) a =
      normalizedPrimitiveLocalCubicCount R 8 (n + 2) a := by
    unfold normalizedLocalCubicCount normalizedPrimitiveLocalCubicCount
    rw [hc]
  rw [he]
  exact normalized_primitive_local_cubic_count_eq h3 7 (n + 2) a

/-- The singular contribution is reduced by the exact factor `q^-5`. -/
theorem normalized_cubic_count_scaling_recurrence
    (h3 : IsUnit (3 : R)) {π : R} (hπ : Irreducible π) (n : ℕ) (b : R) :
    normalizedLocalCubicCount R 8 (n + 3) (π ^ 3 * b) =
      primitiveEightCubicDensity R (π ^ 3 * b) +
        normalizedLocalCubicCount R 8 n b / (Nat.card (ResidueField R) : ℝ) ^ 5 := by
  letI := dvr_power_quotient_finite (R := R) (n + 3)
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hc := local_cubic_count_primitive_add_singular (maximalIdeal R ^ (n + 3))
    (Ideal.pow_le_self (by omega)) 8 (π ^ 3 * b)
  rw [singular_local_cubic_count_scaled hπ n 8 b] at hc
  have hp := normalized_primitive_local_cubic_count_eq h3 7 (n + 2) (π ^ 3 * b)
  change normalizedPrimitiveLocalCubicCount R 8 (n + 2) (π ^ 3 * b) =
    primitiveEightCubicDensity R (π ^ 3 * b) at hp
  rw [← hp]
  unfold normalizedLocalCubicCount normalizedPrimitiveLocalCubicCount
  rw [hc]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, add_div]
  congr 1
  have hd : (Nat.card (ResidueField R) : ℝ) ^ (7 * (n + 3)) =
      (Nat.card (ResidueField R) : ℝ) ^ (7 * n) *
        (Nat.card (ResidueField R) : ℝ) ^ 16 *
          (Nat.card (ResidueField R) : ℝ) ^ 5 := by
    rw [Nat.mul_add, pow_add]
    ring
  norm_num only at hd ⊢
  rw [hd]
  field_simp

theorem unit_mul_uniformizer_pow_not_mem_cube_ideal
    {π : R} (hπ : Irreducible π) (u : Rˣ) {k : ℕ} (hk : k < 3) :
    (u : R) * π ^ k ∉ maximalIdeal R ^ 3 := by
  intro hm
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow,
    IsDiscreteValuationRing.addVal_def' u hπ k] at hm
  have hle : 3 ≤ k := by exact_mod_cast hm
  omega

/-- Nonzero-target local densities eventually stabilize, not merely converge. -/
theorem normalized_cubic_count_unit_pow_eventually_constant
    (h3 : IsUnit (3 : R)) {π : R} (hπ : Irreducible π) (u : Rˣ) (k : ℕ) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
      normalizedLocalCubicCount R 8 e ((u : R) * π ^ k) = σ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 3
    · refine ⟨primitiveEightCubicDensity R ((u : R) * π ^ k), 3, ?_⟩
      intro e he
      have heq : e = (e - 3) + 3 := (Nat.sub_add_cancel he).symm
      rw [heq]
      exact normalized_cubic_count_eq_of_not_mem_cube_ideal h3 (e - 3)
        (unit_mul_uniformizer_pow_not_mem_cube_ideal hπ u hk)
    · have hk3 : 3 ≤ k := Nat.le_of_not_gt hk
      obtain ⟨σ, E, hE⟩ := ih (k - 3) (by omega)
      have ha : (u : R) * π ^ k = π ^ 3 * ((u : R) * π ^ (k - 3)) := by
        calc
          (u : R) * π ^ k = (u : R) * (π ^ (k - 3) * π ^ 3) := by
            rw [← pow_add, Nat.sub_add_cancel hk3]
          _ = π ^ 3 * ((u : R) * π ^ (k - 3)) := by ring
      refine ⟨primitiveEightCubicDensity R ((u : R) * π ^ k) +
        σ / (Nat.card (ResidueField R) : ℝ) ^ 5, E + 3, ?_⟩
      intro e he
      have heq : e = (e - 3) + 3 := by omega
      rw [heq, ha, normalized_cubic_count_scaling_recurrence h3 hπ,
        hE (e - 3) (by omega)]

theorem normalized_cubic_count_eventually_constant_of_ne_zero
    (h3 : IsUnit (3 : R)) {a : R} (ha : a ≠ 0) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
      normalizedLocalCubicCount R 8 e a = σ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  exact normalized_cubic_count_unit_pow_eventually_constant h3 hπ u k

theorem normalized_cubic_count_tendsto_of_ne_zero
    (h3 : IsUnit (3 : R)) {a : R} (ha : a ≠ 0) :
    ∃ σ : ℝ, Filter.Tendsto (fun e => normalizedLocalCubicCount R 8 e a)
      Filter.atTop (nhds σ) := by
  obtain ⟨σ, E, hE⟩ := normalized_cubic_count_eventually_constant_of_ne_zero h3 ha
  refine ⟨σ, ?_⟩
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  exact Filter.eventually_atTop.mpr ⟨E, fun e he => (hE e he).symm⟩

end WaringSiegel

#print axioms WaringSiegel.normalized_cubic_count_scaling_recurrence

#print axioms WaringSiegel.normalized_cubic_count_eventually_constant_of_ne_zero
#print axioms WaringSiegel.normalized_cubic_count_tendsto_of_ne_zero
