import WaringSiegel.WSL4MajorTarget
import WaringSiegel.WSL4EightCubesTarget
import WaringSiegel.LargeKAsymptotic

/-! # User-facing explicit consequences of the verified large-degree theorem

These statements retain the exact local unit-coordinate hypothesis. The
independent cubic endpoint below has no local-solubility premise.
-/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4
variable (K:Type*) [Field K] [NumberField K]

theorem local_conditional_square_bound (k:ℕ) (hk:3≤k) :
    LocalConditionalBound K k (k^2) := by
  apply optimized_localConditionalBound K k (k^2) hk
  simpa only [Nat.cast_pow] using Thresholds.sufficientVariables_le_square k hk

theorem local_conditional_explicit_sqrt_bound (k s:ℕ) (hk:3≤k)
    (hs:(k:ℝ)^2-k-1+2*Real.sqrt (2*((k:ℝ)+1))≤(s:ℝ)) :
    LocalConditionalBound K k s := by
  apply optimized_localConditionalBound K k s hk
  exact_mod_cast (Thresholds.sufficientVariables_explicit_upper k hk).trans hs

theorem local_conditional_large_degree_bound (k s:ℕ) (hk:64≤k)
    (hs:(k:ℝ)^2-k+2*Real.sqrt (2*(k:ℝ))≤(s:ℝ)) :
    LocalConditionalBound K k s := by
  apply optimized_localConditionalBound K k s (by omega)
  exact_mod_cast (Thresholds.sufficientVariables_bounded_remainder k hk).2.trans hs

theorem local_conditional_large_degree_ceiling (k:ℕ) (hk:64≤k) :
    LocalConditionalBound K k ⌈(k:ℝ)^2-k+2*Real.sqrt (2*(k:ℝ))⌉₊ :=
  local_conditional_large_degree_bound K k _ hk (Nat.le_ceil _)

theorem uniform_eight_cubes : UniformWaringSiegelBound 3 8 := eightCubesClaim_verified

#print axioms local_conditional_square_bound
#print axioms local_conditional_explicit_sqrt_bound
#print axioms local_conditional_large_degree_ceiling
#print axioms uniform_eight_cubes
end WaringSiegel.WSL4
