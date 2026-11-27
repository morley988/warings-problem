import WaringSiegel.NumberFieldTargets
import WaringSiegel.CubicAlgebra

/-!
# Cubes in actual finite completions

These results connect global cubic eligibility to literal cube tuples in the
completed integer rings used by `LocalUnitSolvable`. The dyadic case is not
silently assumed: all conclusions here retain their explicit local hypotheses.
-/

noncomputable section
open scoped NumberField BigOperators

namespace WaringSiegel

variable {K : Type*} [Field K] [NumberField K]

theorem eligible_cube_mem_completion_span
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∈
      cubeSpan (v.adicCompletionIntegers K) := by
  apply map_mem_cubeSpan
  exact hν

/-- At any finite completion where 2 is a unit, an eligible global target has
five integral local cube roots, including a unit root. -/
theorem five_cubes_in_completion_of_two_isUnit
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h2 : IsUnit (2 : v.adicCompletionIntegers K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) :
    ∃ x : Fin 5 → v.adicCompletionIntegers K,
      (∑ i, x i ^ 3) = algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧
      ∃ i, IsUnit (x i) :=
  five_cubes_tuple_with_unit h2 (eligible_cube_mem_completion_span v hν)

/-- At a completion where 2 and 3 are units, every global integer, whether or
not eligibility has been separately checked, is four local cubes. -/
theorem four_cubes_in_completion_of_two_three_isUnit
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h2 : IsUnit (2 : v.adicCompletionIntegers K))
    (h3 : IsUnit (3 : v.adicCompletionIntegers K)) (ν : 𝓞 K) :
    ∃ x : Fin 4 → v.adicCompletionIntegers K,
      (∑ i, x i ^ 3) = algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧
      ∃ i, IsUnit (x i) :=
  four_cubes_tuple_with_unit h2 h3 _

/-- The residue-characteristic-three case of the actual completion theorem. -/
theorem five_cubes_in_completion_residue_char_three
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [CharP (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) 3]
    {ν : 𝓞 K} (hν : Eligible 3 ν) :
    ∃ x : Fin 5 → v.adicCompletionIntegers K,
      (∑ i, x i ^ 3) = algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧
      ∃ i, IsUnit (x i) :=
  five_cubes_in_completion_of_two_isUnit v two_isUnit_of_residue_char_three hν

end WaringSiegel

#print axioms WaringSiegel.five_cubes_in_completion_of_two_isUnit
#print axioms WaringSiegel.four_cubes_in_completion_of_two_three_isUnit
#print axioms WaringSiegel.five_cubes_in_completion_residue_char_three
