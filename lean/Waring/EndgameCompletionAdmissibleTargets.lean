import Waring.EndgameCompletionProductEndgame
import Waring.ProductBoxCore
import Waring.HighOrderSeeds

/-!
# The two Waring targets from exactly the intended smooth excesses

The positive core, ordinary minor estimates, strong moments, quantitative
pruning, singular series and singular integral are actual proved inputs.
Only the four displayed smooth admissible excess statements remain as
premises here; they are discharged by the separate seed/policy lane.
-/

noncomputable section
namespace Waring.EndgameCompletion
open SmoothMoments

theorem degree8_productCoreLowerBound : ProductCoreLowerBound 8 8 30 := by
  intro L hL
  exact ProductBox.degree8_product_core_lower L hL

theorem degree9_productCoreLowerBound : ProductCoreLowerBound 9 11 35 := by
  intro L hL
  exact ProductBox.degree9_product_core_lower L hL

theorem waring8_from_intended_admissible_excesses
    (h32 : AdmissibleExcess 8 32 Endgame.delta8_32)
    (h34 : AdmissibleExcess 8 34 Endgame.delta8_34) : WaringBound 8 38 :=
  waring8_from_admissible_and_product_main h32 h34 degree8_productCoreLowerBound

theorem waring9_from_intended_admissible_excesses
    (h38 : AdmissibleExcess 9 38 Endgame.delta9_38)
    (h40 : AdmissibleExcess 9 40 Endgame.delta9_40) : WaringBound 9 46 :=
  waring9_from_admissible_and_product_main h38 h40 degree9_productCoreLowerBound

/-- The exact finite certificate is fully connected to the actual Waring
target; the displayed seed and policy propositions are the remaining gap. -/
theorem waring8_from_high_order_seeds_and_policy
    (hseed : Certificate.HighOrderAdmissibleCurve 8 Certificate.source8)
    (hcoefficientSeed : Certificate.HighOrderAdmissibleCurve 16 Certificate.coefficientSource8)
    (hsound : ∀ i,i<Certificate.policies8.size →
      Certificate.AnalyticPolicySound 8 Certificate.policies8[i]!) : WaringBound 8 38 := by
  obtain ⟨h32,h34⟩ := Certificate.final8_excesses_from_high_order_sources hseed hcoefficientSeed hsound
  exact waring8_from_intended_admissible_excesses h32 h34

theorem waring9_from_high_order_seeds_and_policy
    (hseed : Certificate.HighOrderAdmissibleCurve 9 Certificate.source9)
    (hcoefficientSeed : Certificate.HighOrderAdmissibleCurve 18 Certificate.coefficientSource9)
    (hsound : ∀ i,i<Certificate.policies9.size →
      Certificate.AnalyticPolicySound 9 Certificate.policies9[i]!) : WaringBound 9 46 := by
  obtain ⟨h38,h40⟩ := Certificate.final9_excesses_from_high_order_sources hseed hcoefficientSeed hsound
  exact waring9_from_intended_admissible_excesses h38 h40

#print axioms waring8_from_intended_admissible_excesses
#print axioms waring9_from_intended_admissible_excesses
#print axioms waring8_from_high_order_seeds_and_policy
#print axioms waring9_from_high_order_seeds_and_policy
end Waring.EndgameCompletion
