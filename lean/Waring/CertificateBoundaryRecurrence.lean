import Waring.CertificateBoundaryApplications
import Waring.CertificateRecurrence

/-!
# Boundary errors through the complete frozen recurrence

The actual enlarged-height error is attenuated by every backward step before
reaching the ledger output. These remain algebraic certificate theorems;
the efficient-differencing analytic recurrence is a separate prerequisite.
-/

noncomputable section
namespace Waring.Certificate

private theorem max_left_abs_bound (a x y : ℝ) : |max a x-max a y| ≤ |x-y| := by
  simpa only [max_comm] using abs_max_sub_max_le_abs x y a

/-- Quantitative continuity of the complete terminal-to-first-step objective,
including the major branch, all backward maxima, and the first diagonal. -/
theorem fullObjectiveReal_abs_sub_le (k : Nat) (curve coefficient : Curve)
    (p : Policy) (ev : Evaluation) (piece : Piece)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) (hmass : pieceMass piece ≤ 1)
    (x y : ℝ) :
    |fullObjectiveReal k curve coefficient p ev piece x-
      fullObjectiveReal k curve coefficient p ev piece y| ≤
      boundaryErrorConstant (terminalParameters k curve p)*|x-y| /
        (2 : ℝ)^(recurrenceRows k curve p).length := by
  let params := terminalParameters k curve p
  let R := pieceResidualReal k p coefficient piece params.base params.slope params.scale
  let rows := castRows (recurrenceRows k curve p)
  have hr := pieceResidualReal_abs_sub_le k p coefficient piece params.base params.slope params.scale
    hw hmass x y
  have hterminal := (max_left_abs_bound (ev.major : ℝ) (R x) (R y)).trans hr
  have hback := Recurrence.runBackward_lipschitz rows
    (max (ev.major : ℝ) (R x)) (max (ev.major : ℝ) (R y))
  have hfirst := max_left_abs_bound (firstDiagonal curve p : ℝ)
    (Recurrence.runBackward rows (max (ev.major : ℝ) (R x)))
    (Recurrence.runBackward rows (max (ev.major : ℝ) (R y)))
  calc
    _ = |max (firstDiagonal curve p : ℝ)
          (Recurrence.runBackward rows (max (ev.major : ℝ) (R x)))-
        max (firstDiagonal curve p : ℝ)
          (Recurrence.runBackward rows (max (ev.major : ℝ) (R y)))| := by
      simp only [fullObjectiveReal,params,R,rows]
      congr 1
      ring
    _ ≤ _ := hfirst.trans (hback.trans (div_le_div_of_nonneg_right hterminal (by positivity)))
    _ = _ := by simp only [rows,castRows,List.length_map,params,boundaryErrorConstant]

/-- The stored rounded output remains an upper bound up to the exact
attenuated boundary error, for an actual selected policy piece. -/
theorem entryRecurrenceAssociation_extended (k : Nat) (curve coefficient : Curve)
    (p : Policy) (entry : Entry) (hrec : EntryRecurrenceAssociation k curve p entry)
    (hheight : PolicyHeightAssociation k curve coefficient p entry.evaluation)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    (x κ : ℝ) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x)
    (hhi : x ≤ (terminalParameters k curve p).top) :
    ∃ i : Fin p.pieces.size,
      fullObjectiveReal k curve coefficient p entry.evaluation p.pieces[i.val]! x ≤
        (entry.rounded : ℝ)+boundaryErrorConstant (terminalParameters k curve p)*κ /
          (2 : ℝ)^(recurrenceRows k curve p).length := by
  let params := terminalParameters k curve p
  have htop : 1 ≤ (params.top : ℝ) := by exact_mod_cast hheight.1
  have hclamp := certifiedHeight_bounds htop hκ hlo hhi
  obtain ⟨t,ht,hty⟩ := exists_normalized_coordinate htop hclamp.1
  obtain ⟨i,hi⟩ := policy_pieceChain_covers p hchain ht
  have hp : p.pieces[i.val]! ∈ p.pieces.toList := by
    rw [getElem!_pos p.pieces i.val i.isLt]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)
  have hw := policyGuards_weights_nonneg k p hguard _ hp
  have hm : pieceMass p.pieces[i.val]! ≤ 1 := (hguard.2.2.2.1 _ hp).1.le
  have hcert := entryRecurrenceAssociation_bound k curve coefficient p entry
    hrec hheight hguard i t hi
  change fullObjectiveReal k curve coefficient p entry.evaluation p.pieces[i.val]!
    (1+t*((params.top : ℝ)-1)) ≤ _ at hcert
  rw [hty] at hcert
  have hb := fullObjectiveReal_abs_sub_le k curve coefficient p entry.evaluation
    p.pieces[i.val]! hw hm x (certifiedHeight (params.top : ℝ) x κ)
  have hd := certifiedHeight_distance htop hκ hlo hhi
  have hm' := mul_le_mul_of_nonneg_left hd (boundaryErrorConstant_nonneg params)
  have hdiv := div_le_div_of_nonneg_right hm'
    (show 0 ≤ (2 : ℝ)^(recurrenceRows k curve p).length by positivity)
  have ha := (le_abs_self _).trans (hb.trans hdiv)
  refine ⟨i,?_⟩
  linarith

/-- The complete eighth-degree ledger objective at all actual minor heights. -/
theorem certificate8_full_objective_extended
    (round : Round) (hr : round ∈ heightCheckedRounds8)
    (i : Fin policies8.size) (x κ : ℝ) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x)
    (hhi : x ≤ (terminalParameters 8 round.interpolation.values policies8[i.val]!).top) :
    ∃ j : Fin policies8[i.val]!.pieces.size,
      fullObjectiveReal 8 round.interpolation.values coefficient8.values policies8[i.val]!
        round.entries[i.val]!.evaluation policies8[i.val]!.pieces[j.val]! x ≤
        (round.entries[i.val]!.rounded : ℝ)+
          boundaryErrorConstant (terminalParameters 8 round.interpolation.values policies8[i.val]!)*κ /
            (2 : ℝ)^(recurrenceRows 8 round.interpolation.values policies8[i.val]!).length :=
  entryRecurrenceAssociation_extended 8 round.interpolation.values coefficient8.values
    policies8[i.val]! round.entries[i.val]! (heightCheckedRounds8_recurrence round hr i)
    ((heightCheckedRounds8_association round hr).2 i) (all_policies8_guards i)
    (policies8_piece_chains i) x κ hκ hlo hhi

/-- The complete ninth-degree ledger objective at all actual minor heights. -/
theorem certificate9_full_objective_extended
    (round : Round) (hr : round ∈ heightCheckedRounds9)
    (i : Fin policies9.size) (x κ : ℝ) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x)
    (hhi : x ≤ (terminalParameters 9 round.interpolation.values policies9[i.val]!).top) :
    ∃ j : Fin policies9[i.val]!.pieces.size,
      fullObjectiveReal 9 round.interpolation.values coefficient9.values policies9[i.val]!
        round.entries[i.val]!.evaluation policies9[i.val]!.pieces[j.val]! x ≤
        (round.entries[i.val]!.rounded : ℝ)+
          boundaryErrorConstant (terminalParameters 9 round.interpolation.values policies9[i.val]!)*κ /
            (2 : ℝ)^(recurrenceRows 9 round.interpolation.values policies9[i.val]!).length :=
  entryRecurrenceAssociation_extended 9 round.interpolation.values coefficient9.values
    policies9[i.val]! round.entries[i.val]! (heightCheckedRounds9_recurrence round hr i)
    ((heightCheckedRounds9_association round hr).2 i) (all_policies9_guards i)
    (policies9_piece_chains i) x κ hκ hlo hhi

#print axioms fullObjectiveReal_abs_sub_le
#print axioms certificate8_full_objective_extended
#print axioms certificate9_full_objective_extended
end Waring.Certificate
