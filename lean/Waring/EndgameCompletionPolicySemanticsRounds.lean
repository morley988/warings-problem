import Waring.EndgameCompletionPolicySemanticsChecked
import Waring.CertificateSemantics
import Waring.Endgame

/-! # Analytic propagation through precisely the frozen certificate rounds

This uses an actual admissible entry implication for each stored round. It
does not require or assert soundness of the evaluator on unrelated inputs.
The finite checker still supplies interpolation, rounding and exact writes.
-/

noncomputable section
namespace Waring.Certificate
open SmoothMoments

def RoundEntrySound (k : ℕ) (policies : Array Policy) (coefficient : Curve)
    (round : Round) : Prop :=
  AdmissibleCurve k round.interpolation.values →
  AdmissibleCurve (2*k) coefficient →
  ∀ i : Fin policies.size,
    AdmissibleExponent k (2*policies[i.val]!.halfOrder)
      (round.entries[i.val]!.evaluation.raw : ℝ)

theorem checkedRound_admissible_of_entries (k : ℕ)
    (policies : Array Policy) (coefficient previous : Curve) (round : Round)
    (hcheck : checkRound k policies coefficient previous round=true)
    (hprevious : AdmissibleCurve k previous)
    (hcoefficient : AdmissibleCurve (2*k) coefficient)
    (hentries : RoundEntrySound k policies coefficient round) :
    AdmissibleCurve k round.outputs := by
  rcases checkRound_sound k policies coefficient previous round hcheck with
    ⟨hinputs,hinterp,_hsize,hchecked,houtputs⟩
  have hraw : AdmissibleCurve k round.inputs := hinputs ▸ hprevious
  have hadm := checkedInterpolation_admissible k round.inputs round.interpolation hinterp hraw
  have hshape := (checkInterpolation_sound round.inputs round.interpolation hinterp).1
  rw [← houtputs]
  unfold updatedCurve
  apply admissibleCurve_fold_updates _ _ _ _ hraw
  intro i hi
  have hi' : i<policies.size := List.mem_range.mp hi
  have he := hchecked i hi'
  simp only [checkRoundEntry,Bool.and_eq_true,decide_eq_true_eq] at he
  have hin : policies[i]!.halfOrder<round.interpolation.values.size := hshape ▸ he.1
  have heval := checkEntry_sound k round.interpolation.values coefficient
    policies[i]! round.entries[i]! he.2
  have hnew := hentries hadm hcoefficient ⟨i,hi'⟩
  have hrounded : AdmissibleExponent k (2*policies[i]!.halfOrder)
      (round.entries[i]!.rounded : ℝ) :=
    admissibleExponent_mono hnew (by exact_mod_cast heval.2.1)
  exact admissible_qmin (hadm _ hin) hrounded

theorem final8_admissible_of_frozen_entries
    (hseed : AdmissibleCurve 8 source8)
    (hcoefficientSeed : AdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ round ∈ heightCheckedRounds8,
      RoundEntrySound 8 policies8 coefficient8.values round) :
    AdmissibleCurve 8 final8.values := by
  have hc : AdmissibleCurve 16 coefficient8.values :=
    checkedInterpolation_admissible 16 coefficientSource8 coefficient8
      coefficient8_checked hcoefficientSeed
  have h01 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    source8 round8_01 round8_01_checked hseed hc
    (hsound round8_01 (by simp [heightCheckedRounds8]))
  have h02 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_01.outputs round8_02 round8_02_checked h01 hc
    (hsound round8_02 (by simp [heightCheckedRounds8]))
  have h03 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_02.outputs round8_03 round8_03_checked h02 hc
    (hsound round8_03 (by simp [heightCheckedRounds8]))
  have h04 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_03.outputs round8_04 round8_04_checked h03 hc
    (hsound round8_04 (by simp [heightCheckedRounds8]))
  have h05 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_04.outputs round8_05 round8_05_checked h04 hc
    (hsound round8_05 (by simp [heightCheckedRounds8]))
  have h06 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_05.outputs round8_06 round8_06_checked h05 hc
    (hsound round8_06 (by simp [heightCheckedRounds8]))
  have h07 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_06.outputs round8_07 round8_07_checked h06 hc
    (hsound round8_07 (by simp [heightCheckedRounds8]))
  have h08 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_07.outputs round8_08 round8_08_checked h07 hc
    (hsound round8_08 (by simp [heightCheckedRounds8]))
  have h09 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_08.outputs round8_09 round8_09_checked h08 hc
    (hsound round8_09 (by simp [heightCheckedRounds8]))
  have h10 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_09.outputs round8_10 round8_10_checked h09 hc
    (hsound round8_10 (by simp [heightCheckedRounds8]))
  have h11 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_10.outputs round8_11 round8_11_checked h10 hc
    (hsound round8_11 (by simp [heightCheckedRounds8]))
  have h12 := checkedRound_admissible_of_entries 8 policies8 coefficient8.values
    round8_11.outputs round8_12 round8_12_checked h11 hc
    (hsound round8_12 (by simp [heightCheckedRounds8]))
  exact checkedInterpolation_admissible 8 round8_12.outputs final8
    final8_interpolation_checked h12

theorem final9_admissible_of_frozen_entries
    (hseed : AdmissibleCurve 9 source9)
    (hcoefficientSeed : AdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ round ∈ heightCheckedRounds9,
      RoundEntrySound 9 policies9 coefficient9.values round) :
    AdmissibleCurve 9 final9.values := by
  have hc : AdmissibleCurve 18 coefficient9.values :=
    checkedInterpolation_admissible 18 coefficientSource9 coefficient9
      coefficient9_checked hcoefficientSeed
  have h01 := checkedRound_admissible_of_entries 9 policies9 coefficient9.values
    source9 round9_01 round9_01_checked hseed hc
    (hsound round9_01 (by simp [heightCheckedRounds9]))
  have h02 := checkedRound_admissible_of_entries 9 policies9 coefficient9.values
    round9_01.outputs round9_02 round9_02_checked h01 hc
    (hsound round9_02 (by simp [heightCheckedRounds9]))
  have h03 := checkedRound_admissible_of_entries 9 policies9 coefficient9.values
    round9_02.outputs round9_03 round9_03_checked h02 hc
    (hsound round9_03 (by simp [heightCheckedRounds9]))
  have h04 := checkedRound_admissible_of_entries 9 policies9 coefficient9.values
    round9_03.outputs round9_04 round9_04_checked h03 hc
    (hsound round9_04 (by simp [heightCheckedRounds9]))
  have h05 := checkedRound_admissible_of_entries 9 policies9 coefficient9.values
    round9_04.outputs round9_05 round9_05_checked h04 hc
    (hsound round9_05 (by simp [heightCheckedRounds9]))
  have h06 := checkedRound_admissible_of_entries 9 policies9 coefficient9.values
    round9_05.outputs round9_06 round9_06_checked h05 hc
    (hsound round9_06 (by simp [heightCheckedRounds9]))
  exact checkedInterpolation_admissible 9 round9_06.outputs final9
    final9_interpolation_checked h06

theorem final8_excesses_of_admissible
    (hfinal : AdmissibleCurve 8 final8.values) :
    AdmissibleExcess 8 32 Endgame.delta8_32 ∧
    AdmissibleExcess 8 34 Endgame.delta8_34 := by
  constructor
  · simpa only [Endgame.delta8_32,Rat.cast_div,Rat.cast_ofNat] using
      (delta_admissible_of_eq_some hfinal final8_delta32).1
  · simpa only [Endgame.delta8_34,Rat.cast_div,Rat.cast_ofNat] using
      (delta_admissible_of_eq_some hfinal final8_delta34).1

theorem final9_excesses_of_admissible
    (hfinal : AdmissibleCurve 9 final9.values) :
    AdmissibleExcess 9 38 Endgame.delta9_38 ∧
    AdmissibleExcess 9 40 Endgame.delta9_40 := by
  constructor
  · simpa only [Endgame.delta9_38,Rat.cast_div,Rat.cast_ofNat] using
      (delta_admissible_of_eq_some hfinal final9_delta38).1
  · simpa only [Endgame.delta9_40,Rat.cast_div,Rat.cast_ofNat] using
      (delta_admissible_of_eq_some hfinal final9_delta40).1

#print axioms checkedRound_admissible_of_entries
#print axioms final8_admissible_of_frozen_entries
#print axioms final9_admissible_of_frozen_entries
#print axioms final8_excesses_of_admissible
#print axioms final9_excesses_of_admissible
end Waring.Certificate

