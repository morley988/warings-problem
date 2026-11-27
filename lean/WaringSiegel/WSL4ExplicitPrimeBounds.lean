import WaringSiegel.WSL4ArchOddPrimeTarget
import WaringSiegel.WSL4ExplicitUniformBounds
import WaringSiegel.WSL4MajorQuadraticGlobal

/-! # Explicit unconditional bounds at prime exponents

The large-degree bounds here have no local-solubility premise. The exact
optimized threshold remains available in `oddPrimeGlobalClaim_verified`.
-/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4

theorem uniform_odd_prime_square_bound (k : ℕ) (hkprime : Nat.Prime k) (hk : 3≤k) :
    UniformWaringSiegelBound k (k^2) := by
  intro K _ _
  apply odd_prime_waringSiegelBound K k (k^2) hkprime hk
  simpa only [Nat.cast_pow] using Thresholds.sufficientVariables_le_square k hk

theorem uniform_odd_prime_explicit_sqrt_bound (k s : ℕ)
    (hkprime : Nat.Prime k) (hk : 3≤k)
    (hs : (k:ℝ)^2-k-1+2*Real.sqrt (2*((k:ℝ)+1))≤(s:ℝ)) :
    UniformWaringSiegelBound k s := by
  intro K _ _
  apply odd_prime_waringSiegelBound K k s hkprime hk
  exact_mod_cast (Thresholds.sufficientVariables_explicit_upper k hk).trans hs

theorem uniform_odd_prime_large_degree_ceiling (k : ℕ)
    (hkprime : Nat.Prime k) (hk : 64≤k) :
    UniformWaringSiegelBound k ⌈(k:ℝ)^2-k+2*Real.sqrt (2*(k:ℝ))⌉₊ := by
  intro K _ _
  apply odd_prime_waringSiegelBound K k _ hkprime (by omega)
  exact_mod_cast (Thresholds.sufficientVariables_bounded_remainder k hk).2.trans (Nat.le_ceil _)

theorem uniform_prime_polynomial_bound (k : ℕ) (hkprime : Nat.Prime k) :
    UniformWaringSiegelBound k (8*k^5) := by
  intro K _ _
  by_cases hk2 : k=2
  · subst k
    norm_num
    exact quadratic_waringSiegelBound K
  · exact odd_prime_waringSiegelBound K k _ hkprime (by have := hkprime.two_le; omega)
      (Thresholds.sufficientVariables_le_polynomial_local_bound k
        (by have := hkprime.two_le; omega))

#print axioms uniform_odd_prime_explicit_sqrt_bound
#print axioms uniform_odd_prime_large_degree_ceiling
#print axioms uniform_prime_polynomial_bound
end WaringSiegel.WSL4
