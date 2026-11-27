import Waring.PolicyCompletionMinorSource
import Waring.EndgameCompletionPolicySemanticsMajor

/-! # The actual nonauxiliary terminal estimates in every frozen round -/
noncomputable section
namespace Waring.PolicyCompletionFrozenNonaux
open Certificate SeedCompletionSourceBounds PolicyCompletionMinorSource
open PolicyCompletionTerminalShape PolicyCompletionShapeCap PolicyCompletionResourceFormula
open PolicyCompletionMajorIntegral PolicyCompletionMinorGeometry

theorem policies8_nonaux_dimensions : ∀i : Fin policies8.size,i.val≠0→
    policies8[i.val]!.auxiliaryOrder=none ∧
      (policies8[i.val]!.phi.size=5 ∨ policies8[i.val]!.phi.size=4) := by decide +kernel

theorem policies9_nonaux_dimensions : ∀i : Fin policies9.size,
    policies9[i.val]!.auxiliaryOrder=none ∧
      (policies9[i.val]!.phi.size=6 ∨ policies9[i.val]!.phi.size=5) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policies8_allocations : ∀i : Fin policies8.size,
    ∀j : Fin policies8[i.val]!.pieces.size,
      PieceAllocationValid policies8[i.val]!.phi.size policies8[i.val]!.pieces[j.val]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policies9_allocations : ∀i : Fin policies9.size,
    ∀j : Fin policies9[i.val]!.pieces.size,
      PieceAllocationValid policies9[i.val]!.phi.size policies9[i.val]!.pieces[j.val]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policies8_physical : ∀i : Fin policies8.size,
    ∀j : Fin policies8[i.val]!.pieces.size,∀r,
      ResourcePhysicalShape 8 policies8[i.val]! (resourceAt policies8[i.val]!.pieces[j.val]! r) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policies9_physical : ∀i : Fin policies9.size,
    ∀j : Fin policies9[i.val]!.pieces.size,∀r,
      ResourcePhysicalShape 9 policies9[i.val]! (resourceAt policies9[i.val]!.pieces[j.val]! r) := by decide +kernel

theorem resources_available {k : ℕ} {curve coefficient : Curve} {p : Policy} {ev : Evaluation}
    (h : PolicyMomentAssociation k curve coefficient p ev) :
    ∀i : Fin p.pieces.size,∀r,MomentAvailable coefficient (resourceAt p.pieces[i.val]! r).order := by
  intro i r
  simpa only [resourceAt,getElem!_pos p.pieces[i.val]!.resources r.val r.isLt] using h.2.2.2.2.2.1 i r

theorem policies8_nonaux_reduction (i : Fin policies8.size) (hi : i.val≠0) :
    ∃s : Shape,∃A : ℕ,0<A ∧ policies8[i.val]!.phi.size+extra s+2=8 ∧
      Reduction s 8 policies8[i.val]!.phi.size A := by
  rcases (policies8_nonaux_dimensions i hi).2 with h5|h4
  · refine ⟨.first,53760,by norm_num,?_,?_⟩
    · rw [h5]; rfl
    · rw [h5]; exact reduction8_5
  · refine ⟨.second,26880,by norm_num,?_,?_⟩
    · rw [h4]; rfl
    · rw [h4]; exact reduction8_4

theorem policies9_nonaux_reduction (i : Fin policies9.size) :
    ∃s : Shape,∃A : ℕ,0<A ∧ policies9[i.val]!.phi.size+extra s+2=9 ∧
      Reduction s 9 policies9[i.val]!.phi.size A := by
  rcases (policies9_nonaux_dimensions i).2 with h6|h5
  · refine ⟨.first,967680,by norm_num,?_,?_⟩
    · rw [h6]; rfl
    · rw [h6]; exact reduction9_6
  · refine ⟨.second,483840,by norm_num,?_,?_⟩
    · rw [h5]; rfl
    · rw [h5]; exact reduction9_5

theorem certificate8_nonaux_minor (round : Round) (hr : round∈heightCheckedRounds8)
    (i : Fin policies8.size) (hi : i.val≠0)
    (hcurve : AdmissibleCurve 8 round.interpolation.values)
    (hcoeff : AdmissibleCurve 16 coefficient8.values) {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R=>boxMinorIntegral 8 (terminalHalfOrder policies8[i.val]!) (D*P) P R
        (fun t=>P^(phiReal policies8[i.val]! t)))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  obtain ⟨s,A,hA,hdim,hred⟩:=policies8_nonaux_reduction i hi
  have hmom:=heightCheckedRounds8_moments round hr i
  exact nonauxiliary_minor_source_bound 8 A policies8[i.val]! s (by norm_num) hA hdim hred D hD
    round.interpolation.values coefficient8.values round.entries[i.val]! hcurve hcoeff
    ((heightCheckedRounds8_association round hr).2 i) (heightCheckedRounds8_recurrence round hr i)
    (all_policies8_guards i) (policies8_piece_chains i) (policies8_nonaux_dimensions i hi).1
    (all_policies8_shape i).terminal_pos hmom.2.1 (policies8_allocations i) (policies8_physical i)
    (resources_available hmom)

theorem certificate9_minor (round : Round) (hr : round∈heightCheckedRounds9)
    (i : Fin policies9.size)
    (hcurve : AdmissibleCurve 9 round.interpolation.values)
    (hcoeff : AdmissibleCurve 18 coefficient9.values) {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R=>boxMinorIntegral 9 (terminalHalfOrder policies9[i.val]!) (D*P) P R
        (fun t=>P^(phiReal policies9[i.val]! t)))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  obtain ⟨s,A,hA,hdim,hred⟩:=policies9_nonaux_reduction i
  have hmom:=heightCheckedRounds9_moments round hr i
  exact nonauxiliary_minor_source_bound 9 A policies9[i.val]! s (by norm_num) hA hdim hred D hD
    round.interpolation.values coefficient9.values round.entries[i.val]! hcurve hcoeff
    ((heightCheckedRounds9_association round hr).2 i) (heightCheckedRounds9_recurrence round hr i)
    (all_policies9_guards i) (policies9_piece_chains i) (policies9_nonaux_dimensions i).1
    (all_policies9_shape i).terminal_pos hmom.2.1 (policies9_allocations i) (policies9_physical i)
    (resources_available hmom)

theorem certificate8_nonaux_terminal (round : Round) (hr : round∈heightCheckedRounds8)
    (i : Fin policies8.size) (hi : i.val≠0)
    (hcurve : AdmissibleCurve 8 round.interpolation.values)
    (hcoeff : AdmissibleCurve 16 coefficient8.values) {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R=>boxTerminalIntegral 8 (terminalHalfOrder policies8[i.val]!) (D*P) P R
        (fun t=>P^(phiReal policies8[i.val]! t)))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  have hm:=(certificate8_major_power_bound round hr i hcurve hD).weaken
    (show (round.entries[i.val]!.evaluation.major:ℝ)≤(terminalMaximum round.entries[i.val]!.evaluation:ℝ) by
      exact_mod_cast (heightCheckedRounds8_recurrence round hr i).2.1)
  have hh:=hm.add (certificate8_nonaux_minor round hr i hi hcurve hcoeff hD)
  rw [max_self] at hh
  exact hh.congr (fun P R _ _=>(terminal_integral_split 8 _ (D*P) P R _).symm)

theorem certificate9_terminal (round : Round) (hr : round∈heightCheckedRounds9)
    (i : Fin policies9.size)
    (hcurve : AdmissibleCurve 9 round.interpolation.values)
    (hcoeff : AdmissibleCurve 18 coefficient9.values) {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R=>boxTerminalIntegral 9 (terminalHalfOrder policies9[i.val]!) (D*P) P R
        (fun t=>P^(phiReal policies9[i.val]! t)))
      (terminalMaximum round.entries[i.val]!.evaluation:ℝ) := by
  have hm:=(certificate9_major_power_bound round hr i hcurve hD).weaken
    (show (round.entries[i.val]!.evaluation.major:ℝ)≤(terminalMaximum round.entries[i.val]!.evaluation:ℝ) by
      exact_mod_cast (heightCheckedRounds9_recurrence round hr i).2.1)
  have hh:=hm.add (certificate9_minor round hr i hcurve hcoeff hD)
  rw [max_self] at hh
  exact hh.congr (fun P R _ _=>(terminal_integral_split 9 _ (D*P) P R _).symm)

#print axioms certificate8_nonaux_terminal
#print axioms certificate9_terminal
end Waring.PolicyCompletionFrozenNonaux
