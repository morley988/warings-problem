import WaringSiegel.WSL4LocalSquaresDyadic
import WaringSiegel.CubicLocalTargets

/-! # Five squares with a unit in every actual completed integer ring -/
noncomputable section
open IsLocalRing
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {K:Type*} [Field K] [NumberField K]

theorem eligible_square_mem_completion_span
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν:𝓞 K} (hν:Eligible 2 ν) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν∈squareSpan (v.adicCompletionIntegers K) :=
  map_mem_squareSpan _ hν

theorem eligible_squares_local_five {ν:𝓞 K} (hν:Eligible 2 ν) :
    LocalUnitSolvable 2 5 ν := by
  intro v
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  exact five_squares_henselian_finite_residue (eligible_square_mem_completion_span v hν)

theorem localUnitSolvable_power_succ {k s:ℕ} (hk:0<k) {ν:𝓞 K}
    (h:LocalUnitSolvable k s ν) : LocalUnitSolvable k (s+1) ν := by
  intro v
  exact power_tuple_unit_pad hk (h v)

theorem eligible_squares_local_solvable {s:ℕ} (hs:5≤s) {ν:𝓞 K} (hν:Eligible 2 ν) :
    LocalUnitSolvable 2 s ν := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hs
  clear hs
  induction n with
  | zero => exact eligible_squares_local_five hν
  | succ n ih => exact localUnitSolvable_power_succ (by norm_num) ih

#print axioms eligible_squares_local_five
#print axioms eligible_squares_local_solvable
end WaringSiegel.WSL4Local
