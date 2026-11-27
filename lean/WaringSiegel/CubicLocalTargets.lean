import WaringSiegel.CubicLocal
import WaringSiegel.DenseValuationResidue
import WaringSiegel.ValuationResidueFinite

/-!
# The complete local cubic theorem for number fields

Global cubic eligibility implies a five-cube representation with a unit
coordinate at every finite completion. Both the Henselian property and residue
finiteness of the actual completed integer ring are proved in the imported
modules. No local-solubility hypothesis or residue-characteristic exclusion
remains in the conclusion.

This is a local theorem. The analytic estimates and passage to sufficiently
large positive global representations required for `G_K(3) ≤ 8` are separate.
-/

noncomputable section

open scoped NumberField BigOperators
open IsLocalRing

namespace WaringSiegel

variable {K : Type*} [Field K] [NumberField K]

theorem completionIntegers_residueFinite
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  letI := valuationIntegers_residueFinite v
  exact finite_completionResidue_of_finite_valuationResidue v

/-- Every globally eligible cubic target has a genuine five-cube solution
with a unit coordinate in each completed integer ring. -/
theorem five_cubes_in_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) :
    ∃ x : Fin 5 → v.adicCompletionIntegers K,
      (∑ i, x i ^ 3) = algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧
      ∃ i, IsUnit (x i) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  exact five_cubes_henselian_finite_residue (eligible_cube_mem_completion_span v hν)

/-- In residue characteristic two, four cubes already suffice. -/
theorem four_cubes_in_completion_residue_char_two
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [CharP (ResidueField (v.adicCompletionIntegers K)) 2]
    {ν : 𝓞 K} (hν : Eligible 3 ν) :
    ∃ x : Fin 4 → v.adicCompletionIntegers K,
      (∑ i, x i ^ 3) = algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ∧
      ∃ i, IsUnit (x i) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  exact four_cubes_henselian_residue_char_two (eligible_cube_mem_completion_span v hν)

theorem eligible_localUnitSolvable_five_cubes
    {ν : 𝓞 K} (hν : Eligible 3 ν) : LocalUnitSolvable 3 5 ν := by
  intro v
  exact five_cubes_in_completion v hν

theorem eligible_localUnitSolvable_eight_cubes
    {ν : 𝓞 K} (hν : Eligible 3 ν) : LocalUnitSolvable 3 8 ν :=
  (eligible_localUnitSolvable_five_cubes hν).cubic_succ.cubic_succ.cubic_succ

/-- The local theorem in the variable-count form used by analytic arguments. -/
theorem eligible_cubes_local_solvable
    {s : ℕ} (hs : 5 ≤ s) {ν : 𝓞 K} (hν : Eligible 3 ν) :
    LocalUnitSolvable 3 s ν := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  clear hs
  induction n with
  | zero => exact eligible_localUnitSolvable_five_cubes hν
  | succ n ih => exact ih.cubic_succ

/-- The local obstruction has been discharged. The remaining global cubic
input is exactly the analytic bound with its local-solubility hypothesis. -/
theorem eight_cubes_of_analytic
    (hanalytic : LocalConditionalBound K 3 8) : WaringSiegelBound K 3 8 :=
  bound_of_localConditionalBound hanalytic
    (fun _ hν => eligible_localUnitSolvable_eight_cubes hν)

end WaringSiegel

#print axioms WaringSiegel.completionIntegers_residueFinite
#print axioms WaringSiegel.eligible_localUnitSolvable_five_cubes
#print axioms WaringSiegel.eligible_localUnitSolvable_eight_cubes
#print axioms WaringSiegel.eligible_cubes_local_solvable
#print axioms WaringSiegel.eight_cubes_of_analytic
