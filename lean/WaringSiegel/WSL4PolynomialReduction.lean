import WaringSiegel.WSL4LocalPowerRing
import WaringSiegel.WSL4ExplicitPrimeBounds
import WaringSiegel.WSL4MajorGoodPlaces
import WaringSiegel.WSL4ArchLocalPrimeHelpers

/-! # The precise remaining local obligation for the polynomial bound

The quadratic and prime-exponent cases, all analytic estimates, and every
place at which the exponent is a unit are already proved. This file gives
a checked implication from the remaining strict local power-list bound to
the unchanged `PolynomialGlobalClaim`. The premise is deliberately an
explicit proposition, not an axiom or an asserted theorem.
-/
noncomputable section
open scoped NumberField BigOperators
namespace WaringSiegel.WSL4

/-- The remaining portion of the strict Ramanujam bound: composite
exponents at actual completed integer rings above divisors of the exponent.
The list contains fewer than `8*k^5` terms, leaving room for a unit. -/
def RemainingLocalPowerClaim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ),
    3≤k → ¬Nat.Prime k →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      (k:𝓞 K)∈v.asIdeal →
      ∀ a : v.adicCompletionIntegers K,
        a∈WSL4Local.powerGeneratedRing k (v.adicCompletionIntegers K) →
        ∃ l : List (v.adicCompletionIntegers K),
          l.length<8*k^5 ∧ localPowerListSum k l=a

theorem polynomialGlobalClaim_of_remainingLocalPowerClaim
    (hremaining : RemainingLocalPowerClaim) : PolynomialGlobalClaim := by
  intro K _ _ k hk
  by_cases hprime : Nat.Prime k
  · exact uniform_prime_polynomial_bound k hprime K
  by_cases hk2 : k=2
  · subst k
    norm_num
    exact quadratic_waringSiegelBound K
  have hk3 : 3≤k := by omega
  have hsmall : k+1≤8*k^5 := by
    have hsq := Thresholds.square_le_polynomial_local_bound k (by omega)
    have : k+1≤k^2 := by nlinarith
    omega
  apply bound_of_localConditionalBound
    (optimized_localConditionalBound K k (8*k^5) hk3
      (Thresholds.sufficientVariables_le_polynomial_local_bound k hk3))
  intro ν hν
  apply (localUnitSolvable_iff_at_exponent_divisors k (8*k^5) (by omega) hsmall hν).mpr
  intro v hv
  let f := algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  have hring : f ν∈WSL4Local.powerGeneratedRing k (v.adicCompletionIntegers K) :=
    WSL4Local.map_mem_powerGeneratedRing k f
      ((WSL4Local.eligible_iff_mem_powerGeneratedRing k ν).mp hν)
  have hsub : f ν-1∈WSL4Local.powerGeneratedRing k (v.adicCompletionIntegers K) :=
    (WSL4Local.powerGeneratedRing k _).sub_mem hring
      (WSL4Local.powerGeneratedRing k _).one_mem
  obtain ⟨l,hlen,hl⟩ := hremaining K k hk3 hprime v hv (f ν-1) hsub
  exact unit_power_tuple_of_short_list k (by omega) l (by omega) hl

#print axioms polynomialGlobalClaim_of_remainingLocalPowerClaim
end WaringSiegel.WSL4
