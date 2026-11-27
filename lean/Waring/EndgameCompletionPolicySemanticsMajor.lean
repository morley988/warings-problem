import Waring.EndgameCompletionPolicySemanticsChecked

/-! # Actual major-terminal estimates at the stored certificate exponents -/

noncomputable section
namespace Waring.Certificate
open SmoothMoments SeedCompletionSourceBounds PolicyCompletionMajorSourceBound
open PolicyCompletionMajorIntegral

theorem PolicyShapeAssociation.terminal_pos {k : ℕ} {p : Policy}
    (hshape : PolicyShapeAssociation k p) : 0<terminalHalfOrder p := by
  have hj := hshape.2.2.1
  exact hshape.2.2.2.2.2.2.1 ⟨p.phi.size-1,by omega⟩

theorem PolicyMomentAssociation.first_admissible {k : ℕ} {curve coefficient : Curve}
    {p : Policy} {ev : Evaluation} (h : PolicyMomentAssociation k curve coefficient p ev)
    (hcurve : AdmissibleCurve k curve) :
    AdmissibleExponent k (2*(p.halfOrder-1))
      ((moment curve (2*(p.halfOrder-1))).getD 0 : ℝ) :=
  moment_getD_admissible hcurve h.1

theorem PolicyMomentAssociation.path_admissible {k : ℕ} {curve coefficient : Curve}
    {p : Policy} {ev : Evaluation} (h : PolicyMomentAssociation k curve coefficient p ev)
    (hcurve : AdmissibleCurve k curve) (i : Fin p.phi.size) :
    AdmissibleExponent k (2*p.path[i.val]!)
      ((moment curve (2*p.path[i.val]!)).getD 0 : ℝ) :=
  moment_getD_admissible hcurve (h.2.2.2.1 i)

theorem PolicyMomentAssociation.backward_admissible {k : ℕ} {curve coefficient : Curve}
    {p : Policy} {ev : Evaluation} (h : PolicyMomentAssociation k curve coefficient p ev)
    (hcurve : AdmissibleCurve k curve) (i : Fin (p.phi.size-1)) :
    AdmissibleExponent k (2*(2*p.path[i.val]!-p.path[i.val+1]!))
      ((moment curve (2*(2*p.path[i.val]!-p.path[i.val+1]!))).getD 0 : ℝ) :=
  moment_getD_admissible hcurve (h.2.2.2.2.1 i)

theorem PolicyMomentAssociation.resource_admissible {k : ℕ} {curve coefficient : Curve}
    {p : Policy} {ev : Evaluation} (h : PolicyMomentAssociation k curve coefficient p ev)
    (hcoefficient : AdmissibleCurve (2*k) coefficient) (i : Fin p.pieces.size)
    (r : Fin p.pieces[i.val]!.resources.size) :
    AdmissibleExcess (2*k) p.pieces[i.val]!.resources[r.val]!.order
      ((delta (2*k) coefficient p.pieces[i.val]!.resources[r.val]!.order).getD 0 : ℝ) :=
  delta_getD_admissible hcoefficient (h.2.2.2.2.2.1 i r)

theorem policy_major_power_bound {k : ℕ} {curve coefficient : Curve}
    {p : Policy} {ev : Evaluation} (hshape : PolicyShapeAssociation k p)
    (hguard : PolicyAnalyticGuards k p)
    (hmom : PolicyMomentAssociation k curve coefficient p ev)
    (hcurve : AdmissibleCurve k curve) {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R => boxMajorIntegral k (terminalHalfOrder p) (D*P) P R
        (fun i => P^(phiReal p i))) (ev.major : ℝ) := by
  rw [hmom.2.2.2.2.2.2,terminalMajorFormula_cast]
  exact major_source_power_bound (by have hh:=hshape.1; omega)
    hshape.2.2.2.1 (hshape.terminal_pos) hD (phiReal p)
    (fun i => (phiReal_pos hguard i).le)
    (phiReal_shift_pos (by have hh:=hshape.1; omega) hguard)
    (delta_getD_admissible hcurve hmom.2.1)

theorem certificate8_major_power_bound (round : Round) (hr : round∈heightCheckedRounds8)
    (i : Fin policies8.size) (hcurve : AdmissibleCurve 8 round.interpolation.values)
    {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R => boxMajorIntegral 8 (terminalHalfOrder policies8[i.val]!) (D*P) P R
        (fun t => P^(phiReal policies8[i.val]! t)))
      (round.entries[i.val]!.evaluation.major : ℝ) :=
  policy_major_power_bound (all_policies8_shape i) (all_policies8_guards i)
    (heightCheckedRounds8_moments round hr i) hcurve hD

theorem certificate9_major_power_bound (round : Round) (hr : round∈heightCheckedRounds9)
    (i : Fin policies9.size) (hcurve : AdmissibleCurve 9 round.interpolation.values)
    {D : ℝ} (hD : 1≤D) :
    SourcePowerBound
      (fun P R => boxMajorIntegral 9 (terminalHalfOrder policies9[i.val]!) (D*P) P R
        (fun t => P^(phiReal policies9[i.val]! t)))
      (round.entries[i.val]!.evaluation.major : ℝ) :=
  policy_major_power_bound (all_policies9_shape i) (all_policies9_guards i)
    (heightCheckedRounds9_moments round hr i) hcurve hD

#print axioms policy_major_power_bound
#print axioms certificate8_major_power_bound
#print axioms certificate9_major_power_bound
end Waring.Certificate
