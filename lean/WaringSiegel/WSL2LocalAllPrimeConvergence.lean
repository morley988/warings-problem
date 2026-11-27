import WaringSiegel.WSL2LocalRamifiedSeeds
import WaringSiegel.WSL2LocalConvergence

/-!
# Local-density convergence at every finite prime

Ramified cubic branches give constant normalized primitive counts beyond the
explicit precision `2v(3)+1`. The singular scaling recursion then proves that
the full normalized counts stabilize for every nonzero target.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped BigOperators

namespace WaringSiegel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem primitive_local_cubic_count_ramified_at
    (h3 : (3 : R) ≠ 0) (s r e : ℕ)
    (he : e = (cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R) (a : R) :
    primitiveLocalCubicSolutionCount R (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by omega)) (s + 1) a =
      Nat.card (PrimitiveCubicBranchSeeds R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * (r + cubicDerivativeOrder R) + cubicDerivativeOrder R) := by
  subst e
  exact primitive_local_cubic_count_ramified_exact h3 s r a

def primitiveEightCubicDensityAllPrimes
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (a : R) : ℝ :=
  (Nat.card (PrimitiveCubicBranchSeeds R 8 a) : ℝ) /
    (Nat.card (ResidueField R) : ℝ) ^ (6 * cubicDerivativeOrder R + 7)

theorem normalized_primitive_local_cubic_count_ramified_eq
    (h3 : (3 : R) ≠ 0) (n : ℕ) (hn : 2 * cubicDerivativeOrder R ≤ n) (a : R) :
    normalizedPrimitiveLocalCubicCount R 8 n a = primitiveEightCubicDensityAllPrimes R a := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold normalizedPrimitiveLocalCubicCount primitiveEightCubicDensityAllPrimes
  rw [primitive_local_cubic_count_ramified_at h3 7 (n - 2 * cubicDerivativeOrder R)
    (n + 1) (by omega)]
  simp only [Nat.cast_mul, Nat.cast_pow]
  norm_num only
  have he : 7 * (n + 1) =
      (7 * (n - 2 * cubicDerivativeOrder R + cubicDerivativeOrder R) + cubicDerivativeOrder R) +
        (6 * cubicDerivativeOrder R + 7) := by omega
  rw [he, pow_add]
  field_simp
  simp only [pow_add]
  ring

theorem normalized_primitive_local_cubic_count_all_primes_tendsto
    (h3 : (3 : R) ≠ 0) (a : R) :
    Tendsto (fun n => normalizedPrimitiveLocalCubicCount R 8 n a) atTop
      (𝓝 (primitiveEightCubicDensityAllPrimes R a)) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  exact eventually_atTop.mpr ⟨2 * cubicDerivativeOrder R,
    fun n hn => (normalized_primitive_local_cubic_count_ramified_eq h3 n hn a).symm⟩

theorem normalized_cubic_count_ramified_eq_of_not_mem_cube_ideal
    (h3 : (3 : R) ≠ 0) (n : ℕ) (hn : 2 * cubicDerivativeOrder R ≤ n + 2)
    {a : R} (ha : a ∉ maximalIdeal R ^ 3) :
    normalizedLocalCubicCount R 8 (n + 3) a = primitiveEightCubicDensityAllPrimes R a := by
  letI := dvr_power_quotient_finite (R := R) (n + 3)
  have hc := local_cubic_count_primitive_add_singular (maximalIdeal R ^ (n + 3))
    (Ideal.pow_le_self (by omega)) 8 a
  rw [singular_local_cubic_count_zero n 8 ha, add_zero] at hc
  have he : normalizedLocalCubicCount R 8 (n + 3) a =
      normalizedPrimitiveLocalCubicCount R 8 (n + 2) a := by
    unfold normalizedLocalCubicCount normalizedPrimitiveLocalCubicCount
    rw [hc]
  rw [he]
  exact normalized_primitive_local_cubic_count_ramified_eq h3 (n + 2) hn a

theorem normalized_cubic_count_scaling_recurrence_all_primes
    (h3 : (3 : R) ≠ 0) {π : R} (hπ : Irreducible π) (n : ℕ)
    (hn : 2 * cubicDerivativeOrder R ≤ n + 2) (b : R) :
    normalizedLocalCubicCount R 8 (n + 3) (π ^ 3 * b) =
      primitiveEightCubicDensityAllPrimes R (π ^ 3 * b) +
        normalizedLocalCubicCount R 8 n b / (Nat.card (ResidueField R) : ℝ) ^ 5 := by
  letI := dvr_power_quotient_finite (R := R) (n + 3)
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hc := local_cubic_count_primitive_add_singular (maximalIdeal R ^ (n + 3))
    (Ideal.pow_le_self (by omega)) 8 (π ^ 3 * b)
  rw [singular_local_cubic_count_scaled hπ n 8 b] at hc
  have hp := normalized_primitive_local_cubic_count_ramified_eq h3 (n + 2) hn (π ^ 3 * b)
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

/-- Stabilization for a unit times any power of a uniformizer, including at 3. -/
theorem normalized_cubic_count_all_primes_unit_pow_eventually_constant
    (h3 : (3 : R) ≠ 0) {π : R} (hπ : Irreducible π) (u : Rˣ) (k : ℕ) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
      normalizedLocalCubicCount R 8 e ((u : R) * π ^ k) = σ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 3
    · refine ⟨primitiveEightCubicDensityAllPrimes R ((u : R) * π ^ k),
        2 * cubicDerivativeOrder R + 3, ?_⟩
      intro e he
      have heq : e = (e - 3) + 3 := by omega
      rw [heq]
      exact normalized_cubic_count_ramified_eq_of_not_mem_cube_ideal h3 (e - 3)
        (by omega) (unit_mul_uniformizer_pow_not_mem_cube_ideal hπ u hk)
    · have hk3 : 3 ≤ k := Nat.le_of_not_gt hk
      obtain ⟨σ, E, hE⟩ := ih (k - 3) (by omega)
      have ha : (u : R) * π ^ k = π ^ 3 * ((u : R) * π ^ (k - 3)) := by
        calc
          (u : R) * π ^ k = (u : R) * (π ^ (k - 3) * π ^ 3) := by
            rw [← pow_add, Nat.sub_add_cancel hk3]
          _ = π ^ 3 * ((u : R) * π ^ (k - 3)) := by ring
      refine ⟨primitiveEightCubicDensityAllPrimes R ((u : R) * π ^ k) +
        σ / (Nat.card (ResidueField R) : ℝ) ^ 5,
          max E (2 * cubicDerivativeOrder R) + 3, ?_⟩
      intro e he
      have heq : e = (e - 3) + 3 := by omega
      rw [heq, ha, normalized_cubic_count_scaling_recurrence_all_primes h3 hπ
        (e - 3) (by omega), hE (e - 3) (by omega)]

/-- Genuine full local-density convergence at every finite prime for every
nonzero target. No local-density existence premise is required. -/
theorem normalized_cubic_count_all_primes_eventually_constant_of_ne_zero
    (h3 : (3 : R) ≠ 0) {a : R} (ha : a ≠ 0) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
      normalizedLocalCubicCount R 8 e a = σ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  exact normalized_cubic_count_all_primes_unit_pow_eventually_constant h3 hπ u k

theorem normalized_cubic_count_all_primes_tendsto_of_ne_zero
    (h3 : (3 : R) ≠ 0) {a : R} (ha : a ≠ 0) :
    ∃ σ : ℝ, Tendsto (fun e => normalizedLocalCubicCount R 8 e a) atTop (𝓝 σ) := by
  obtain ⟨σ, E, hE⟩ := normalized_cubic_count_all_primes_eventually_constant_of_ne_zero h3 ha
  refine ⟨σ, ?_⟩
  apply Tendsto.congr' _ tendsto_const_nhds
  exact eventually_atTop.mpr ⟨E, fun e he => (hE e he).symm⟩

end WaringSiegel

#print axioms WaringSiegel.normalized_primitive_local_cubic_count_all_primes_tendsto

#print axioms WaringSiegel.normalized_cubic_count_all_primes_tendsto_of_ne_zero
