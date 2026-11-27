import WaringSiegel.NormAdicComplete
import Mathlib.NumberTheory.NumberField.FinitePlaces

/-!
# Hensel's lemma in the actual completed integer rings

No Henselian hypothesis is postulated here. The completed field is complete;
its valuation ring is closed; and its maximal-ideal powers are the norm balls
defined by a uniformizer. These facts give algebraic adic completeness and hence
Mathlib's proved Hensel theorem.
-/

noncomputable section

open scoped NumberField WithZero

namespace WaringSiegel

variable {K : Type*} [Field K] [NumberField K]

theorem completionIntegers_completeSpace
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (v.adicCompletionIntegers K) :=
  (Valued.isClosed_valuationSubring (v.adicCompletion K)).isComplete.completeSpace_coe

theorem completionIntegers_maximalIdeal_pow_norm_ball
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) (n : ℕ) :
    ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
      Metric.closedBall 0 (‖π‖ ^ n) := by
  letI : IsDiscreteValuationRing
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have hval := (Valuation.valuationSubring.integers
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow
      hπ n
  change ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
    Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) = _ at hval
  rw [hval]
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  change Valued.v (x : v.adicCompletion K) ≤
    Valued.v (π : v.adicCompletion K) ^ n ↔ _
  rw [← map_pow]
  change Valued.v (x : v.adicCompletion K) ≤
    Valued.v ((π : v.adicCompletion K) ^ n) ↔ _
  rw [← Valued.toNormedField.norm_le_iff]
  simp only [norm_pow]
  rfl

theorem completionIntegers_irreducible_norm_lt_one
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) : ‖π‖ < 1 := by
  change ‖(π : v.adicCompletion K)‖ < 1
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mp
    ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit)

theorem completionIntegers_isAdicComplete
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
  letI := completionIntegers_completeSpace v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  exact isAdicComplete_of_norm_balls _ (norm_nonneg π)
    (completionIntegers_irreducible_norm_lt_one v hπ)
    (completionIntegers_maximalIdeal_pow_norm_ball v hπ)

theorem completionIntegers_henselianLocalRing
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    HenselianLocalRing (v.adicCompletionIntegers K) := by
  letI := completionIntegers_isAdicComplete v
  exact henselianLocalRing_of_isAdicComplete

end WaringSiegel

#print axioms WaringSiegel.completionIntegers_henselianLocalRing
