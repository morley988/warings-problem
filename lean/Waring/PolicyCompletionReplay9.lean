import Waring.PolicyCompletionReplay8

/-! # Actual analytic replay for new ninth-power policy parameters

The conditions are explicit finite shape, guard, allocation and source-cap
facts. Both original and alternate numerical data remain independent of the
analytic proof, and all moment inputs retain their genuine admissibility.
-/
noncomputable section
namespace Waring.PolicyCompletionReplay9
open Certificate SmoothMoments SeedCompletionSourceBounds SeedCompletionNaturalBox
open PolicyCompletionFrozenNonaux PolicyCompletionFrozenTerminal PolicyCompletionBackwardRunner
open PolicyCompletionMinorSource PolicyCompletionMinorGeometry PolicyCompletionMajorIntegral
open PolicyCompletionTerminalShape PolicyCompletionShapeCap PolicyCompletionResourceFormula

def PolicyConditions (p : Policy) : Prop :=
  PolicyShapeAssociation 9 p ∧ PolicyAnalyticGuards 9 p ∧
  PieceChain 0 1 p.pieces.toList ∧ p.auxiliaryOrder=none ∧
  (p.phi.size=6 ∨ p.phi.size=5) ∧
  (∀ i : Fin p.pieces.size, PieceAllocationValid p.phi.size p.pieces[i.val]!) ∧
  (∀ i : Fin p.pieces.size, ∀ r : Fin p.pieces[i.val]!.resources.size,
    ResourcePhysicalShape 9 p (resourceAt p.pieces[i.val]! r))

instance (p : Policy) : Decidable (PolicyConditions p) := by
  unfold PolicyConditions
  infer_instance

theorem policy_terminal (p : Policy) (curve coefficient : Curve) (entry : Entry)
    (hconditions : PolicyConditions p)
    (hheight : PolicyHeightAssociation 9 curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation 9 curve p entry)
    (hmom : PolicyMomentAssociation 9 curve coefficient p entry.evaluation)
    (hcurve : AdmissibleCurve 9 curve) (hcoeff : AdmissibleCurve 18 coefficient) :
    SourcePowerBound
      (powerBoxCross 9 (terminalHalfOrder p) ((2:ℝ)^p.phi.size) (phiReal p))
      (terminalMaximum entry.evaluation:ℝ) := by
  rcases hconditions with ⟨hshape,hguard,hchain,haux,hdim,halloc,hphysical⟩
  have hmajor := (policy_major_power_bound hshape hguard hmom hcurve
    (D:=(2:ℝ)^p.phi.size) (one_le_pow₀ (by norm_num))).weaken
    (show (entry.evaluation.major:ℝ)≤(terminalMaximum entry.evaluation:ℝ) by
      exact_mod_cast hrec.2.1)
  have hred : ∃ s : Shape, ∃ A : ℕ, 0<A ∧ p.phi.size+extra s+2=9 ∧
      Reduction s 9 p.phi.size A := by
    rcases hdim with h6|h5
    · refine ⟨.first,967680,by norm_num,?_,?_⟩
      · rw [h6]; rfl
      · rw [h6]; exact reduction9_6
    · refine ⟨.second,483840,by norm_num,?_,?_⟩
      · rw [h5]; rfl
      · rw [h5]; exact reduction9_5
  obtain ⟨s,A,hA,hdim,hred⟩ := hred
  have hminor := nonauxiliary_minor_source_bound 9 A p s (by norm_num) hA hdim hred
    ((2:ℝ)^p.phi.size) (one_le_pow₀ (by norm_num)) curve coefficient entry hcurve hcoeff
    hheight hrec hguard hchain haux hshape.terminal_pos hmom.2.1 halloc hphysical
    (resources_available hmom)
  have hh := hmajor.add hminor
  rw [max_self] at hh
  apply hh.congr
  intro P R hP hR
  exact (terminal_integral_split 9 _ _ P R _).symm.trans
    (boxTerminalIntegral_eq_powerBoxCross 9 _ _ P R _ (zero_lt_one.trans_le hP)
      (fun t=>(phiReal_pos hguard t).le))

theorem policy_entry_admissible (p : Policy) (curve coefficient : Curve) (entry : Entry)
    (hconditions : PolicyConditions p)
    (hheight : PolicyHeightAssociation 9 curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation 9 curve p entry)
    (hmom : PolicyMomentAssociation 9 curve coefficient p entry.evaluation)
    (hcurve : AdmissibleCurve 9 curve) (hcoeff : AdmissibleCurve 18 coefficient) :
    AdmissibleExponent 9 (2*p.halfOrder) (entry.evaluation.raw:ℝ) :=
  policy_entry_of_terminal hconditions.1 hconditions.2.1 hmom hrec hcurve
    (policy_terminal p curve coefficient entry hconditions hheight hrec hmom hcurve hcoeff)

theorem round_entry_sound (policies : Array Policy) (coefficient : Curve) (round : Round)
    (hconditions : ∀ i : Fin policies.size, PolicyConditions policies[i.val]!)
    (hheight : RoundHeightAssociation 9 policies coefficient round)
    (hrec : RoundRecurrenceAssociation 9 policies round)
    (hmom : RoundMomentAssociation 9 policies coefficient round) :
    RoundEntrySound 9 policies coefficient round := by
  intro hcurve hcoeff i
  exact policy_entry_admissible policies[i.val]! round.interpolation.values coefficient
    round.entries[i.val]! (hconditions i) (hheight.2 i) (hrec i) (hmom i) hcurve hcoeff

#print axioms policy_entry_admissible
#print axioms round_entry_sound
end Waring.PolicyCompletionReplay9
