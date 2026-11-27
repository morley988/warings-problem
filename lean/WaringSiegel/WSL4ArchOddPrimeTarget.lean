import WaringSiegel.WSL4ArchLocalPrime
import WaringSiegel.WSL4MajorTarget
import WaringSiegel.WSL3MomentThresholdRange

/-! # The unchanged unconditional odd-prime Waring--Siegel target -/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4

theorem odd_prime_waringSiegelBound
    (K : Type*) [Field K] [NumberField K]
    (k s : ℕ) (hkprime : Nat.Prime k) (hk : 3≤k)
    (hs : Thresholds.sufficientVariables k≤(s:ℤ)) :
    WaringSiegelBound K k s := by
  apply bound_of_localConditionalBound (optimized_localConditionalBound K k s hk hs)
  intro ν hν
  exact eligible_odd_prime_local_solvable k hkprime hk
    (Thresholds.admissible_variables_gt_twice_degree k s hk hs).le hν

theorem oddPrimeGlobalClaim_verified : OddPrimeGlobalClaim := by
  intro K _ _ k s hkprime hk hs
  exact odd_prime_waringSiegelBound K k s hkprime hk hs

#print axioms odd_prime_waringSiegelBound
#print axioms oddPrimeGlobalClaim_verified
end WaringSiegel.WSL4
