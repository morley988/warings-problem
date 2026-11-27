import Waring.PolicyCompletionFrozenEntries

/-! # Analytic replay of the unchanged degree-eight policies on new exact curves

Every analytic estimate is already proved. The only additional metadata are
finite identities tying an arbitrary concrete round to its exact evaluator.
-/
noncomputable section
namespace Waring.PolicyCompletionReplay8
open Certificate SmoothMoments SeedCompletionSourceBounds SeedCompletionNaturalBox
open PolicyCompletionFrozenNonaux PolicyCompletionFrozenTerminal PolicyCompletionBackwardRunner
open PolicyCompletionAuxiliaryMinor PolicyCompletionAuxiliaryParameters
open PolicyCompletionMinorSource PolicyCompletionMinorGeometry PolicyCompletionMajorIntegral

theorem policy_terminal (curve coefficient : Curve) (entry : Entry) (i : Fin policies8.size)
    (hheight : PolicyHeightAssociation 8 curve coefficient policies8[i.val]! entry.evaluation)
    (hrec : EntryRecurrenceAssociation 8 curve policies8[i.val]! entry)
    (hmom : PolicyMomentAssociation 8 curve coefficient policies8[i.val]! entry.evaluation)
    (hcurve : AdmissibleCurve 8 curve) (hcoeff : AdmissibleCurve 16 coefficient) :
    SourcePowerBound
      (powerBoxCross 8 (terminalHalfOrder policies8[i.val]!)
        ((2:ℝ)^policies8[i.val]!.phi.size) (phiReal policies8[i.val]!))
      (terminalMaximum entry.evaluation:ℝ) := by
  have hmajor := (policy_major_power_bound (all_policies8_shape i) (all_policies8_guards i)
    hmom hcurve (D:=(2:ℝ)^policies8[i.val]!.phi.size) (one_le_pow₀ (by norm_num))).weaken
    (show (entry.evaluation.major:ℝ)≤(terminalMaximum entry.evaluation:ℝ) by exact_mod_cast hrec.2.1)
  have hminor : SourcePowerBound
      (fun P R=>boxMinorIntegral 8 (terminalHalfOrder policies8[i.val]!)
        (((2:ℝ)^policies8[i.val]!.phi.size)*P) P R (fun t=>P^(phiReal policies8[i.val]! t)))
      (terminalMaximum entry.evaluation:ℝ):=by
    by_cases hi : i.val=0
    · have hi' : i=(⟨0,by decide⟩:Fin policies8.size):=Fin.ext hi
      subst i
      have h20 : MomentAvailable curve 20:=by
        have ht:=hmom.2.2.1
        rwa [frozen_full_order] at ht
      have hD : (2:ℝ)^policies8[0]!.phi.size=64:=by
        have hj : policies8[0]!.phi.size=6:=by decide +kernel
        rw [hj]
        norm_num
      simpa only [Fin.val_mk,hD,frozen_half_order] using
        auxiliary_minor_source_bound curve coefficient entry hcurve hcoeff hheight hrec
          (all_policies8_guards ⟨0,by decide⟩) (policies8_piece_chains ⟨0,by decide⟩) h20
          (policies8_allocations ⟨0,by decide⟩) (policies8_physical ⟨0,by decide⟩)
          (resources_available hmom)
    · obtain ⟨s,A,hA,hdim,hred⟩:=policies8_nonaux_reduction i hi
      exact nonauxiliary_minor_source_bound 8 A policies8[i.val]! s (by norm_num) hA hdim hred
        ((2:ℝ)^policies8[i.val]!.phi.size) (one_le_pow₀ (by norm_num)) curve coefficient entry
        hcurve hcoeff hheight hrec (all_policies8_guards i) (policies8_piece_chains i)
        (policies8_nonaux_dimensions i hi).1 (all_policies8_shape i).terminal_pos hmom.2.1
        (policies8_allocations i) (policies8_physical i) (resources_available hmom)
  have hh:=hmajor.add hminor
  rw [max_self] at hh
  apply hh.congr
  intro P R hP hR
  exact (terminal_integral_split 8 _ _ P R _).symm.trans
    (boxTerminalIntegral_eq_powerBoxCross 8 _ _ P R _ (zero_lt_one.trans_le hP)
      (fun t=>(phiReal_pos (all_policies8_guards i) t).le))

theorem policy_entry_admissible (curve coefficient : Curve) (entry : Entry) (i : Fin policies8.size)
    (hheight : PolicyHeightAssociation 8 curve coefficient policies8[i.val]! entry.evaluation)
    (hrec : EntryRecurrenceAssociation 8 curve policies8[i.val]! entry)
    (hmom : PolicyMomentAssociation 8 curve coefficient policies8[i.val]! entry.evaluation)
    (hcurve : AdmissibleCurve 8 curve) (hcoeff : AdmissibleCurve 16 coefficient) :
    AdmissibleExponent 8 (2*policies8[i.val]!.halfOrder) (entry.evaluation.raw:ℝ):=
  policy_entry_of_terminal (all_policies8_shape i) (all_policies8_guards i) hmom hrec hcurve
    (policy_terminal curve coefficient entry i hheight hrec hmom hcurve hcoeff)

theorem round_entry_sound (coefficient : Curve) (round : Round)
    (hheight : RoundHeightAssociation 8 policies8 coefficient round)
    (hrec : RoundRecurrenceAssociation 8 policies8 round)
    (hmom : RoundMomentAssociation 8 policies8 coefficient round) :
    RoundEntrySound 8 policies8 coefficient round := by
  intro hcurve hcoeff i
  exact policy_entry_admissible round.interpolation.values coefficient round.entries[i.val]! i
    (hheight.2 i) (hrec i) (hmom i) hcurve hcoeff

#print axioms policy_entry_admissible
#print axioms round_entry_sound
end Waring.PolicyCompletionReplay8
