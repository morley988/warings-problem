import WaringSiegel.WSL2LocalCount

/-!
# Uniform lower bounds for actual local cubic densities

For each finite completion there is one positive constant, independent of the
eligible target, bounding all sufficiently precise normalized solution counts
from below. Thus any convergent local density has that positive lower bound.
Convergence of the full local density is not assumed in the count theorem.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped NumberField BigOperators

namespace WaringSiegel

def normalizedLocalCubicCount
    (R : Type*) [CommRing R] [IsLocalRing R] (s e : ℕ) (a : R) : ℝ :=
  (localCubicSolutionCount R (maximalIdeal R ^ e) s a : ℝ) /
    (Nat.card (ResidueField R) : ℝ) ^ ((s - 1) * e)

theorem normalized_local_cubic_count_lower_of_count
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    {s E n : ℕ} {a : R}
    (hc : Nat.card (ResidueField R) ^ (s * n) ≤
      localCubicSolutionCount R (maximalIdeal R ^ (n + E)) (s + 1) a) :
    1 / (Nat.card (ResidueField R) : ℝ) ^ (s * E) ≤
      normalizedLocalCubicCount R (s + 1) (n + E) a := by
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hc' : (Nat.card (ResidueField R) : ℝ) ^ (s * n) ≤
      (localCubicSolutionCount R (maximalIdeal R ^ (n + E)) (s + 1) a : ℝ) := by
    exact_mod_cast hc
  unfold normalizedLocalCubicCount
  rw [Nat.add_sub_cancel]
  calc
    1 / (Nat.card (ResidueField R) : ℝ) ^ (s * E) =
        (Nat.card (ResidueField R) : ℝ) ^ (s * n) /
          (Nat.card (ResidueField R) : ℝ) ^ (s * (n + E)) := by
      rw [Nat.mul_add, pow_add, ← div_div, div_self (pow_ne_zero _ hq.ne')]
    _ ≤ _ := div_le_div_of_nonneg_right hc' (pow_pos hq _).le

variable {K : Type*} [Field K] [NumberField K]

theorem completionIntegers_charZero
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CharZero (v.adicCompletionIntegers K) :=
  charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K))

/-- The count bound with the explicit manuscript precision `2 v(3) + 1`. -/
theorem completion_cubic_count_lower_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) (n : ℕ) :
    Nat.card (ResidueField (v.adicCompletionIntegers K)) ^ (7 * n) ≤
      localCubicSolutionCount (v.adicCompletionIntegers K)
        (maximalIdeal (v.adicCompletionIntegers K) ^
          (n + cubicLocalPrecision (v.adicCompletionIntegers K))) 8
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  obtain ⟨x, hx, hu⟩ := cube_tuple_unit_first (s := 7)
    (eligible_localUnitSolvable_eight_cubes hν v)
  have hE := cubic_stability_ideal_eq_power (v.adicCompletionIntegers K) (by norm_num)
  have h := local_cubic_count_lower_of_unit_tuple x hu _ hE.le n
  simpa only [hx] using h

def completionCubicDensityLowerBound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  1 / (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) ^
    (7 * cubicLocalPrecision (v.adicCompletionIntegers K))

theorem completionCubicDensityLowerBound_pos
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 < completionCubicDensityLowerBound v := by
  letI := completionIntegers_residueFinite v
  apply div_pos zero_lt_one
  apply pow_pos
  exact_mod_cast Nat.card_pos

theorem completion_normalized_cubic_count_lower_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) {e : ℕ}
    (he : cubicLocalPrecision (v.adicCompletionIntegers K) ≤ e) :
    completionCubicDensityLowerBound v ≤
      normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) := by
  letI := completionIntegers_residueFinite v
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le he
  have h := normalized_local_cubic_count_lower_of_count
    (completion_cubic_count_lower_bound v hν n)
  simpa only [completionCubicDensityLowerBound, Nat.add_comm] using h

/-- A genuine prime-power solution-count bound at every finite prime,
including primes above 3. The exponent `E` is chosen before the target. -/
theorem completion_cubic_count_uniform_lower
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ E : ℕ, 0 < E ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ∀ n : ℕ,
      Nat.card (ResidueField (v.adicCompletionIntegers K)) ^ (7 * n) ≤
        localCubicSolutionCount (v.adicCompletionIntegers K)
          (maximalIdeal (v.adicCompletionIntegers K) ^ (n + E)) 8
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  obtain ⟨E, hE0, hE⟩ := exists_cubic_stability_exponent
    (v.adicCompletionIntegers K) (by norm_num)
  refine ⟨E, hE0, ?_⟩
  intro ν hν n
  obtain ⟨x, hx, hu⟩ := cube_tuple_unit_first (s := 7)
    (eligible_localUnitSolvable_eight_cubes hν v)
  have h := local_cubic_count_lower_of_unit_tuple x hu E hE.le n
  simpa only [hx] using h

/-- The normalized counts have a positive lower bound uniform over all
eligible targets and all sufficiently large precisions. -/
theorem completion_cubic_normalized_count_uniform_lower
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ E : ℕ, 0 < E ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ∀ e : ℕ, E ≤ e →
      1 / (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) ^ (7 * E) ≤
        normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) := by
  letI := completionIntegers_residueFinite v
  obtain ⟨E, hE0, hE⟩ := completion_cubic_count_uniform_lower v
  refine ⟨E, hE0, ?_⟩
  intro ν hν e he
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le he
  have h := normalized_local_cubic_count_lower_of_count (hE ν hν n)
  simpa only [Nat.add_comm] using h

/-- Any local-density limit of the actual counts inherits a uniform positive
lower bound. This result does not postulate that such a limit is positive. -/
theorem completion_cubic_density_limits_uniformly_positive
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ∀ σ : ℝ,
      Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 σ) → c ≤ σ := by
  letI := completionIntegers_residueFinite v
  obtain ⟨E, -, hE⟩ := completion_cubic_normalized_count_uniform_lower v
  have hq : 0 < (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) := by
    exact_mod_cast Nat.card_pos
  refine ⟨1 / (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) ^ (7 * E),
    div_pos zero_lt_one (pow_pos hq _), ?_⟩
  intro ν hν σ hσ
  exact ge_of_tendsto hσ (eventually_atTop.mpr ⟨E, fun e he => hE ν hν e he⟩)

end WaringSiegel

#print axioms WaringSiegel.completion_cubic_count_uniform_lower
#print axioms WaringSiegel.completion_cubic_count_lower_bound
#print axioms WaringSiegel.completion_normalized_cubic_count_lower_bound
#print axioms WaringSiegel.completion_cubic_normalized_count_uniform_lower
#print axioms WaringSiegel.completion_cubic_density_limits_uniformly_positive
