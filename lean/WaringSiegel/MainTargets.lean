import WaringSiegel.NumberFieldTargets
import WaringSiegel.Thresholds

/-!
# Requested theorem types, kept separate from proved supporting lemmas

These are definitions of the goals. There is deliberately no theorem here
asserting a goal whose analytic/local proof has not been kernel checked.
`TargetAudit.lean` searches for closed proof terms of these exact types.
-/

namespace WaringSiegel

/-- The optimized degree-uniform analytic theorem with its local hypothesis. -/
def LargeKAnalyticClaim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k s : ℕ),
    3 ≤ k → Thresholds.sufficientVariables k ≤ (s : ℤ) →
      LocalConditionalBound K k s

/-- The all-exponent unconditional consequence removing the older exponential term. -/
def PolynomialGlobalClaim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ),
    2 ≤ k → WaringSiegelBound K k (8 * k ^ 5)

/-- The stronger unconditional consequence at odd prime exponents. -/
def OddPrimeGlobalClaim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k s : ℕ),
    Nat.Prime k → 3 ≤ k → Thresholds.sufficientVariables k ≤ (s : ℤ) →
      WaringSiegelBound K k s

/-- The requested all-field cubic target, with positivity and norm control. -/
def EightCubesClaim : Prop := UniformWaringSiegelBound 3 8

end WaringSiegel
