import Waring.PolicyCompletionFrozenTerminal
import Waring.PolicyCompletionBackwardRunner
import Waring.EndgameCompletionPolicySemanticsRounds

/-! # Unconditional analytic validity of the frozen policy entries

The hypotheses below are solely genuine admissibility of the input curves.
Every source recurrence, major/minor terminal, resource estimate, and literal
finite association needed for these fixed rounds has been proved.
-/
noncomputable section
namespace Waring.PolicyCompletionFrozenEntries
open Certificate SmoothMoments PolicyCompletionFrozenTerminal PolicyCompletionBackwardRunner

theorem certificate8_round_entry_sound (round : Round) (hr : round∈heightCheckedRounds8) :
    RoundEntrySound 8 policies8 coefficient8.values round := by
  intro hcurve hcoeff i
  exact policy_entry_of_terminal (all_policies8_shape i) (all_policies8_guards i)
    (heightCheckedRounds8_moments round hr i) (heightCheckedRounds8_recurrence round hr i) hcurve
    (certificate8_cross_terminal round hr i hcurve hcoeff)

theorem certificate9_round_entry_sound (round : Round) (hr : round∈heightCheckedRounds9) :
    RoundEntrySound 9 policies9 coefficient9.values round := by
  intro hcurve hcoeff i
  exact policy_entry_of_terminal (all_policies9_shape i) (all_policies9_guards i)
    (heightCheckedRounds9_moments round hr i) (heightCheckedRounds9_recurrence round hr i) hcurve
    (certificate9_cross_terminal round hr i hcurve hcoeff)

theorem final8_admissible_from_actual_seeds
    (hseed : AdmissibleCurve 8 source8) (hcoefficientSeed : AdmissibleCurve 16 coefficientSource8) :
    AdmissibleCurve 8 final8.values :=
  final8_admissible_of_frozen_entries hseed hcoefficientSeed certificate8_round_entry_sound

theorem final9_admissible_from_actual_seeds
    (hseed : AdmissibleCurve 9 source9) (hcoefficientSeed : AdmissibleCurve 18 coefficientSource9) :
    AdmissibleCurve 9 final9.values :=
  final9_admissible_of_frozen_entries hseed hcoefficientSeed certificate9_round_entry_sound

#print axioms certificate8_round_entry_sound
#print axioms certificate9_round_entry_sound
#print axioms final8_admissible_from_actual_seeds
#print axioms final9_admissible_from_actual_seeds
end Waring.PolicyCompletionFrozenEntries
