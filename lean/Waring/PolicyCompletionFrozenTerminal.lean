import Waring.PolicyCompletionFrozenNonaux
import Waring.PolicyCompletionAuxiliaryMinor
import Waring.SeedCompletionNaturalChronological

/-! # Every frozen terminal bounds its actual chronological source cross integral -/
noncomputable section
namespace Waring.PolicyCompletionFrozenTerminal
open Certificate SeedCompletionSourceBounds SeedCompletionNaturalBox
open PolicyCompletionFrozenNonaux PolicyCompletionAuxiliaryMinor PolicyCompletionAuxiliaryParameters
open PolicyCompletionMajorIntegral PolicyCompletionMinorGeometry PolicyCompletionMajorPowerRanges

theorem certificate8_auxiliary_terminal (round : Round) (hr : round∈heightCheckedRounds8)
    (hcurve : AdmissibleCurve 8 round.interpolation.values)
    (hcoeff : AdmissibleCurve 16 coefficient8.values) :
    SourcePowerBound
      (fun P R=>boxTerminalIntegral 8 (terminalHalfOrder policies8[0]!) (64*P) P R
        (fun t=>P^(phiReal policies8[0]! t)))
      (terminalMaximum round.entries[0]!.evaluation:ℝ) := by
  let i : Fin policies8.size:=⟨0,by decide⟩
  have hmom:=heightCheckedRounds8_moments round hr i
  have hterminal : MomentAvailable round.interpolation.values 20:=by
    have hh:=hmom.2.2.1
    rwa [frozen_full_order] at hh
  have hminor:=auxiliary_minor_source_bound round.interpolation.values coefficient8.values
    round.entries[0]! hcurve hcoeff ((heightCheckedRounds8_association round hr).2 i)
    (heightCheckedRounds8_recurrence round hr i) (all_policies8_guards i)
    (policies8_piece_chains i) hterminal (policies8_allocations i) (policies8_physical i)
    (resources_available hmom)
  have hminor' : SourcePowerBound
      (fun P R=>boxMinorIntegral 8 (terminalHalfOrder policies8[0]!) (64*P) P R
        (fun t=>P^(phiReal policies8[0]! t)))
      (terminalMaximum round.entries[0]!.evaluation:ℝ):=by
    simpa only [frozen_half_order] using hminor
  have hmajor:=(certificate8_major_power_bound round hr i hcurve (D:=64) (by norm_num)).weaken
    (show (round.entries[0]!.evaluation.major:ℝ)≤(terminalMaximum round.entries[0]!.evaluation:ℝ) by
      exact_mod_cast (heightCheckedRounds8_recurrence round hr i).2.1)
  have hh:=hmajor.add hminor'
  rw [max_self] at hh
  exact hh.congr (fun P R _ _=>(terminal_integral_split 8 _ (64*P) P R _).symm)

theorem certificate8_terminal (round : Round) (hr : round∈heightCheckedRounds8)
    (i : Fin policies8.size)
    (hcurve : AdmissibleCurve 8 round.interpolation.values)
    (hcoeff : AdmissibleCurve 16 coefficient8.values) :
    SourcePowerBound
      (fun P R=>boxTerminalIntegral 8 (terminalHalfOrder policies8[i.val]!)
        (((2:ℝ)^policies8[i.val]!.phi.size)*P) P R (fun t=>P^(phiReal policies8[i.val]! t)))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  by_cases hi : i.val=0
  · have hD : (2:ℝ)^policies8[0]!.phi.size=64:=by
      have hj : policies8[0]!.phi.size=6:=by decide +kernel
      rw [hj]
      norm_num
    have hifin : i=(⟨0,by decide⟩:Fin policies8.size):=Fin.ext hi
    subst i
    simpa only [Fin.val_mk,hD] using certificate8_auxiliary_terminal round hr hcurve hcoeff
  · exact certificate8_nonaux_terminal round hr i hi hcurve hcoeff (one_le_pow₀ (by norm_num))

theorem boxTerminalIntegral_eq_powerBoxCross {j : ℕ} (k s : ℕ) (D P R : ℝ)
    (φ : Fin j→ℝ) (hP : 0<P) (hφ : ∀i,0≤φ i) :
    boxTerminalIntegral k s (D*P) P R (fun i=>P^(φ i))=powerBoxCross k s D φ P R := by
  unfold boxTerminalIntegral powerBoxCross boxCrossMoment
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),boxSmoothLength_power hP D φ hφ]

theorem certificate8_cross_terminal (round : Round) (hr : round∈heightCheckedRounds8)
    (i : Fin policies8.size)
    (hcurve : AdmissibleCurve 8 round.interpolation.values)
    (hcoeff : AdmissibleCurve 16 coefficient8.values) :
    SourcePowerBound
      (powerBoxCross 8 (terminalHalfOrder policies8[i.val]!)
        ((2:ℝ)^policies8[i.val]!.phi.size) (phiReal policies8[i.val]!))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  apply (certificate8_terminal round hr i hcurve hcoeff).congr
  intro P R hP hR
  exact boxTerminalIntegral_eq_powerBoxCross 8 _ _ P R _ (zero_lt_one.trans_le hP)
    (fun t=>(phiReal_pos (all_policies8_guards i) t).le)

theorem certificate9_cross_terminal (round : Round) (hr : round∈heightCheckedRounds9)
    (i : Fin policies9.size)
    (hcurve : AdmissibleCurve 9 round.interpolation.values)
    (hcoeff : AdmissibleCurve 18 coefficient9.values) :
    SourcePowerBound
      (powerBoxCross 9 (terminalHalfOrder policies9[i.val]!)
        ((2:ℝ)^policies9[i.val]!.phi.size) (phiReal policies9[i.val]!))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  apply (certificate9_terminal round hr i hcurve hcoeff
    (D:=(2:ℝ)^policies9[i.val]!.phi.size) (one_le_pow₀ (by norm_num))).congr
  intro P R hP hR
  exact boxTerminalIntegral_eq_powerBoxCross 9 _ _ P R _ (zero_lt_one.trans_le hP)
    (fun t=>(phiReal_pos (all_policies9_guards i) t).le)

#print axioms certificate8_cross_terminal
#print axioms certificate9_cross_terminal
end Waring.PolicyCompletionFrozenTerminal
