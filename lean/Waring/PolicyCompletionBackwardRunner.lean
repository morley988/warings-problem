import Waring.PolicyCompletionPrefixStages

/-! # The actual chronological backward recurrence reaches the stored raw entry -/
noncomputable section
namespace Waring.PolicyCompletionBackwardRunner
open Certificate PolicyCompletionPrefixStages SeedCompletionNaturalBox SeedCompletionSourceBounds
open SmoothMoments

def descendingRows (k : ℕ) (curve : Curve) (p : Policy) (n : ℕ) : List (Q×Q) :=
  (List.range n).map (fun t=>recurrenceRow k curve p (n-t))

theorem descendingRows_succ (k : ℕ) (curve : Curve) (p : Policy) (n : ℕ) :
    descendingRows k curve p (n+1)=recurrenceRow k curve p (n+1)::descendingRows k curve p n := by
  simp [descendingRows,List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one]

theorem recurrenceRows_eq_descending (k : ℕ) (curve : Curve) (p : Policy) :
    recurrenceRows k curve p=descendingRows k curve p (p.phi.size-1) := by
  unfold recurrenceRows descendingRows
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  dsimp only [Function.comp_def]
  congr 1
  omega

theorem backward_prefix_bound {k : ℕ} {p : Policy} {curve coefficient : Curve}
    {ev : Evaluation} (hshape : PolicyShapeAssociation k p)
    (hguard : PolicyAnalyticGuards k p)
    (hmom : PolicyMomentAssociation k curve coefficient p ev)
    (hcurve : AdmissibleCurve k curve) (n : ℕ) (hn : n+1≤p.phi.size)
    {χ : ℝ}
    (hX : SourcePowerBound
      (powerBoxCross k p.path[n]! ((2:ℝ)^(n+1)) (prefixPhi p (n+1))) χ) :
    SourcePowerBound (powerBoxCross k p.path[0]! 2 (prefixPhi p 1))
      (Recurrence.runBackward (castRows (descendingRows k curve p n)) χ) := by
  induction n generalizing χ with
  | zero=>simpa [descendingRows,castRows,Recurrence.runBackward] using hX
  | succ n ih=>
    have hs:=policy_backward_step hshape hguard hmom hcurve
      (j:=n+1) (by omega) (by omega) hX
    have hs' : SourcePowerBound
        (powerBoxCross k p.path[n]! ((2:ℝ)^(n+1)) (prefixPhi p (n+1)))
        (((recurrenceRow k curve p (n+1)).1:ℝ)+max ((recurrenceRow k curve p (n+1)).2:ℝ) χ/2):=by
      simpa only [Nat.add_sub_cancel] using hs
    have hi:=ih (by omega) hs'
    simpa only [Nat.succ_eq_add_one,descendingRows_succ,castRows,List.map_cons,
      Recurrence.runBackward,Recurrence.backward] using hi

/-- Genuine terminal bounds plus genuine curve admissibility prove the exact
stored raw exponent. The analytic recurrence is the counted source theorem;
the list runner only identifies its chronological stages with the ledger. -/
theorem policy_entry_of_terminal {k : ℕ} {p : Policy} {curve coefficient : Curve}
    {entry : Entry} (hshape : PolicyShapeAssociation k p)
    (hguard : PolicyAnalyticGuards k p)
    (hmom : PolicyMomentAssociation k curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation k curve p entry)
    (hcurve : AdmissibleCurve k curve)
    (hterminal : SourcePowerBound
      (powerBoxCross k (terminalHalfOrder p) ((2:ℝ)^p.phi.size) (phiReal p))
      (terminalMaximum entry.evaluation:ℝ)) :
    AdmissibleExponent k (2*p.halfOrder) (entry.evaluation.raw:ℝ) := by
  have hk : 2≤k:=by have hh:=hshape.1; omega
  have hp : 2≤p.halfOrder:=hshape.2.1
  have hj : 1≤p.phi.size:=hshape.2.2.1
  have hsize : p.phi.size<k:=by have hh:=hshape.2.2.2.1; omega
  have hpath : p.path[0]! =p.halfOrder-1:=hshape.2.2.2.2.2.1
  have hn : p.phi.size-1+1=p.phi.size:=by omega
  have hterm : SourcePowerBound
      (powerBoxCross k p.path[p.phi.size-1]! ((2:ℝ)^(p.phi.size-1+1))
        (prefixPhi p (p.phi.size-1+1))) (terminalMaximum entry.evaluation:ℝ):=by
    rw [hn,prefixPhi_full]
    exact hterminal
  have hb:=backward_prefix_bound hshape hguard hmom hcurve (p.phi.size-1) (by omega) hterm
  rw [←recurrenceRows_eq_descending] at hb
  let s : ℕ:=p.halfOrder-2
  have hs1 : s+1=p.halfOrder-1:=by dsimp [s]; omega
  have hs2 : s+2=p.halfOrder:=by dsimp [s]; omega
  obtain ⟨hψ,hψk,_⟩:=next_phi_constraints (by omega : 0<k) hguard hsize
    (show 0<p.phi.size by omega)
  have hU : AdmissibleExponent k (2*(s+1))
      ((moment curve (2*(p.halfOrder-1))).getD 0:ℝ):=by
    rw [hs1]
    exact hmom.first_admissible hcurve
  have hX : SourcePowerBound
      (powerBoxCross k (s+1) 2 (Fin.snoc emptyPhi (p.phi[0]!:ℝ)))
      (Recurrence.runBackward (castRows (recurrenceRows k curve p)) (terminalMaximum entry.evaluation:ℝ)):=by
    rw [hs1,←hpath,←prefixPhi_zero p,←prefixPhi_snoc]
    exact hb
  have H:=first_box_admissible_snoc hk hψ hψk hU hX
  rw [hs2] at H
  have hsR : (s:ℝ)+1=(p.halfOrder:ℝ)-1:=by
    have hh : s+1+1=p.halfOrder:=by omega
    have hc : (s:ℝ)+1+1=(p.halfOrder:ℝ):=by exact_mod_cast hh
    linarith
  rw [hsR] at H
  convert H using 1
  rw [hrec.2.2.2.1]
  simp only [Rat.cast_add,cast_qmax,runBackwardQ_cast,firstOffset_cast,
    firstDiagonal_cast curve (show 0<p.phi.size by omega),Nat.cast_mul,Nat.cast_ofNat]
  ring

#print axioms backward_prefix_bound
#print axioms policy_entry_of_terminal
end Waring.PolicyCompletionBackwardRunner
