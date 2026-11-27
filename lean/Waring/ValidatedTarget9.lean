import Waring.SeedCompletionAlternate9Seeds
import Waring.SeedCompletionEarly18Seeds
import Waring.PolicyCompletionEarly9Final
import Waring.EndgameCompletionCriterion

/-! # The unconditional classical Waring bound in degree nine

This declaration is assembled solely from actual seed moments, exact finite
policy replay, and the proved analytic endgame. The original frozen
certificate and original seed tables remain separate and unchanged.
-/
noncomputable section
namespace Waring

theorem waring_bound_9_46 : WaringBound 9 46 := by
  have hfinal := Certificate.early_final9_admissible
    SeedCompletionAlternate9Seeds.alternate_source9_admissible
    SeedCompletionEarly18Seeds.early_coefficient9_admissible
  obtain ⟨h38, h40⟩ := Certificate.early_final9_excesses hfinal
  exact EndgameCompletion.waring9_from_admissible_excess_criterion h38 h40
    Certificate.early9_strict_criterion

#print axioms waring_bound_9_46
end Waring
