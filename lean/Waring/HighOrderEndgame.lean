import Waring.EndgameFromPublishedInputs
import Waring.HighOrderSeeds

/-!
# Conditional Waring bounds with only the remaining high-order seed inputs

The elementary moments of order zero, two and four are supplied by proved
estimates. Published source admissibility begins at moment order six. All
policy, ordinary arc, strong pruning and positive main-term assumptions
remain visible and must still be discharged for an unconditional result.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped ENNReal Topology

namespace Waring.HighOrderEndgame
open SmoothMoments MixedEndgame AdmissibleMinorArc Certificate Pruning

/-- A complete conditional path to the degree-eight Waring bound. Pruning
little-o is proved from the displayed ordinary pruning moment and strong full
smooth moment; it is no longer a separate analytic premise. -/
theorem waring8_from_high_order_source_estimates
    (hseed : HighOrderAdmissibleCurve 8 source8)
    (hcoefficientSeed : HighOrderAdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R W : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop → Tendsto W atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n^η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*(P n)^(30 : ℝ) ≤
          arcContribution 8 8 30 (P n) (R n) n (core n)) →
        ∀ Cf Cg : ℝ, 0 < Cf → 0 < Cg →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (pruning n) ≤
          ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ)))) →
        (∀ᶠ n in atTop, smoothMoment 8 42 (P n) (R n) ≤ Cg*(P n)^34) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(63+epsilon8)) →
        WaringBound 8 38 :=
  EndgameFromPublishedInputs.waring8_from_source_estimates
    (source8_admissible_of_high hseed)
    (coefficientSource8_admissible_of_high hcoefficientSeed) hsound

/-- Degree nine needs no additional smooth source moment for pruning, because
the pointwise trivial smooth bound and ordinary 11th moment suffice. -/
theorem waring9_from_high_order_source_estimates
    (hseed : HighOrderAdmissibleCurve 9 source9)
    (hcoefficientSeed : HighOrderAdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ i, i < policies9.size → AnalyticPolicySound 9 policies9[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R W : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop → Tendsto W atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n^η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*(P n)^(37 : ℝ) ≤
          arcContribution 9 11 35 (P n) (R n) n (core n)) →
        ∀ Cf : ℝ, 0 < Cf →
        (∀ᶠ n in atTop, ordinaryArcMoment 9 11 (P n) (pruning n) ≤
          ENNReal.ofReal (Cf*(P n)^2*(W n)^(-(1/18 : ℝ)))) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 9 90 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(80+epsilon9)) →
        WaringBound 9 46 :=
  EndgameFromPublishedInputs.waring9_from_source_estimates
    (source9_admissible_of_high hseed)
    (coefficientSource9_admissible_of_high hcoefficientSeed) hsound

#print axioms waring8_from_high_order_source_estimates
#print axioms waring9_from_high_order_source_estimates
end Waring.HighOrderEndgame
