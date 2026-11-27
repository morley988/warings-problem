import WaringPrior.Primitive
import WaringPrior.Fifteen
import WaringPrior.UnramifiedPowers
import WaringSiegel.WSL4MajorTarget

open scoped NumberField
namespace WaringSmallK.Local

theorem split_dyadic_quartic (K : Type) [Field K] [NumberField K]
    (h : DyadicCompletionsAreZ2 K) : WaringSiegel.WaringSiegelBound K 4 16 :=
  split_dyadic_quartic_of_largeK WaringSiegel.WSL4.largeKAnalyticClaim_verified K h

theorem unramified_quartic (K : Type) [Field K] [NumberField K]
    (h : UnramifiedAtTwo K) : WaringSiegel.WaringSiegelBound K 4 16 :=
  unramified_quartic_of_largeK WaringSiegel.WSL4.largeKAnalyticClaim_verified K h

theorem unramified_power_of_two (K : Type) [Field K] [NumberField K]
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ¬ IsUnit (2:v.adicCompletionIntegers K) →
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)=Ideal.span {(2:v.adicCompletionIntegers K)})
    (r s : ℕ) (hr : 3 ≤ 2^r) (hlocal : 4*2^r ≤ s)
    (hs : WaringSiegel.Thresholds.sufficientVariables (2^r) ≤ (s:ℤ)) :
    WaringSiegel.WaringSiegelBound K (2^r) s :=
  WaringSmallK.UnramifiedPowers.global_of_analytic WaringSiegel.WSL4.largeKAnalyticClaim_verified
    K he r s hr hlocal hs

theorem unramified_quartic_fifteen (K : Type) [Field K] [NumberField K] (he : UnramifiedAtTwo K)
    (hu : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ¬IsUnit (4:v.adicCompletionIntegers K) →
      ∃ u : v.adicCompletionIntegers K, u^2+u+1=0) :
    WaringSiegel.WaringSiegelBound K 4 15 :=
  fifteen_of_largeK WaringSiegel.WSL4.largeKAnalyticClaim_verified K he hu

theorem unramified_eighth (K : Type) [Field K] [NumberField K]
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ¬ IsUnit (2:v.adicCompletionIntegers K) →
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)=Ideal.span {(2:v.adicCompletionIntegers K)}) :
    WaringSiegel.WaringSiegelBound K 8 61 := by
  apply unramified_power_of_two K he 3 61 (by decide) (by decide)
  change WaringSiegel.Thresholds.sufficientVariables 8 ≤ (61:ℤ)
  rw [WaringSiegel.Thresholds.variables_8]

end WaringSmallK.Local
#print axioms WaringSmallK.Local.unramified_eighth
#print axioms WaringSmallK.Local.unramified_quartic_fifteen
#print axioms WaringSmallK.Local.unramified_power_of_two
#print axioms WaringSmallK.Local.unramified_quartic
#print axioms WaringSmallK.Local.split_dyadic_quartic
