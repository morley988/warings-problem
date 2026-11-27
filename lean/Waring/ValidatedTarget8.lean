import Waring.SeedCompletionAlternate8Seeds
import Waring.SeedCompletionEarly16Curve
import Waring.PolicyCompletionEarly8Final
import Waring.EndgameCompletionCriterion

/-! # The unconditional classical Waring bound in degree eight

This declaration is assembled solely from actual seed moments, exact finite
policy replay, and the proved analytic endgame. The original frozen
certificate and original seed tables remain separate and unchanged.
-/
noncomputable section
namespace Waring

theorem waring_bound_8_38 : WaringBound 8 38 := by
  have hfinal := Certificate.early_final8_admissible
    SeedCompletionAlternate8Seeds.alternate_source8_admissible
    SeedCompletionEarly16Curve.early_coefficient8_admissible
  obtain ⟨h32,h34⟩ := Certificate.early_final8_excesses hfinal
  exact EndgameCompletion.waring8_from_admissible_excess_criterion h32 h34
    Certificate.early8_strict_criterion

#print axioms waring_bound_8_38
end Waring
