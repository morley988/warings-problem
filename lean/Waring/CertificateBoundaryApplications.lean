import Waring.CertificateHeightBoundary

/-!
# The frozen certificates cover the actual lower height boundary

The stored endpoint bounds now control every actual height in [1-kappa,top],
with an explicit linear error. The epsilon form chooses a small positive eta
for a boundary displacement rho*eta. All resource weights and piece selections
are the actual ones in the checked policy; no global L>=P assumption is made.
-/

noncomputable section
namespace Waring.Certificate

/-- Every height in the certified interval has a normalized coordinate,
including the degenerate case top=1. -/
theorem exists_normalized_coordinate {top y : ℝ} (htop : 1 ≤ top)
    (hy : y ∈ Set.Icc 1 top) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ 1+t*(top-1)=y := by
  by_cases heq : top=1
  · have hy1 : y=1 := le_antisymm (heq ▸ hy.2) hy.1
    refine ⟨0,by constructor <;> norm_num,?_⟩
    simp [hy1]
  · have hpos : 0 < top-1 := by have ht := lt_of_le_of_ne htop (Ne.symm heq); linarith
    refine ⟨(y-1)/(top-1),⟨div_nonneg (by linarith [hy.1]) hpos.le,?_⟩,?_⟩
    · apply (div_le_iff₀ hpos).mpr
      linarith [hy.2]
    · rw [div_mul_cancel₀ _ hpos.ne']
      ring

def boundaryErrorConstant (params : TerminalParameters) : ℝ :=
  |(params.slope : ℝ)|+2*|(params.scale : ℝ)|

theorem boundaryErrorConstant_nonneg (params : TerminalParameters) :
    0 ≤ boundaryErrorConstant params := by unfold boundaryErrorConstant; positivity

/-- The actual guarded weighted saving loses at most 2*kappa on clamping. -/
theorem policy_pieceSaving_clamped_lower (k : Nat) (p : Policy) (coefficient : Curve)
    (hguard : PolicyAnalyticGuards k p) (piece : Piece) (hp : piece ∈ p.pieces.toList)
    {top x κ : ℝ} (htop : 1 ≤ top) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x) (hhi : x ≤ top) :
    min 1 (pieceSavingReal k p coefficient piece (certifiedHeight top x κ))-2*κ ≤
      min 1 (pieceSavingReal k p coefficient piece x) := by
  have hw := policyGuards_weights_nonneg k p hguard piece hp
  have hm : pieceMass piece ≤ 1 := (hguard.2.2.2.1 piece hp).1.le
  have hb := capped_pieceSavingReal_abs_sub_le_two k p coefficient piece hw hm
    x (certifiedHeight top x κ)
  have hd := certifiedHeight_distance htop hκ hlo hhi
  have ha := (abs_le.mp hb).1
  linarith

/-- The same stored endpoints control an actual height down to 1-kappa.
The existential piece is selected by the certified clamped height. -/
theorem policyHeightAssociation_extended (k : Nat) (curve coefficient : Curve)
    (p : Policy) (ev : Evaluation) (h : PolicyHeightAssociation k curve coefficient p ev)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    (x κ : ℝ) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x)
    (hhi : x ≤ (terminalParameters k curve p).top) :
    ∃ i : Fin p.pieces.size,
      let params := terminalParameters k curve p
      pieceResidualReal k p coefficient p.pieces[i.val]! params.base params.slope params.scale x ≤
        max (ev.pieces[i.val]!.endpoints[0]!.exponent : ℝ)
          (ev.pieces[i.val]!.endpoints[1]!.exponent : ℝ)+boundaryErrorConstant params*κ := by
  let params := terminalParameters k curve p
  have htop : 1 ≤ (params.top : ℝ) := by exact_mod_cast h.1
  have hclamp := certifiedHeight_bounds htop hκ hlo hhi
  obtain ⟨t,ht,hty⟩ := exists_normalized_coordinate htop hclamp.1
  obtain ⟨i,hi⟩ := policy_pieceChain_covers p hchain ht
  have hp : p.pieces[i.val]! ∈ p.pieces.toList := by
    rw [getElem!_pos p.pieces i.val i.isLt]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)
  have hw := policyGuards_weights_nonneg k p hguard _ hp
  have hm : pieceMass p.pieces[i.val]! ≤ 1 := (hguard.2.2.2.1 _ hp).1.le
  have hcert := policyHeightAssociation_all_heights k curve coefficient p ev h hguard i t hi
  change pieceResidualReal k p coefficient p.pieces[i.val]! params.base params.slope params.scale
    (1+t*((params.top : ℝ)-1)) ≤ _ at hcert
  rw [hty] at hcert
  exact ⟨i,pieceResidualReal_clamped_upper k p coefficient p.pieces[i.val]!
    params.base params.slope params.scale hw hm htop hκ hlo hhi hcert⟩

/-- All lower-boundary displacement can be included in an arbitrary epsilon
loss, with a uniformly positive smoothness exponent. -/
theorem policyHeightAssociation_extended_epsilon (k : Nat) (curve coefficient : Curve)
    (p : Policy) (ev : Evaluation) (h : PolicyHeightAssociation k curve coefficient p ev)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    {rho ε : ℝ} (hrho : 0 ≤ rho) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, 1-rho*η ≤ x → x ≤ (terminalParameters k curve p).top →
      ∃ i : Fin p.pieces.size,
        let params := terminalParameters k curve p
        pieceResidualReal k p coefficient p.pieces[i.val]! params.base params.slope params.scale x ≤
          max (ev.pieces[i.val]!.endpoints[0]!.exponent : ℝ)
            (ev.pieces[i.val]!.endpoints[1]!.exponent : ℝ)+ε := by
  let K := boundaryErrorConstant (terminalParameters k curve p)
  have hK : 0 ≤ K := boundaryErrorConstant_nonneg _
  let η := ε/(K*rho+1)
  have hden : 0 < K*rho+1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hid : η*(K*rho+1)=ε := div_mul_cancel₀ ε hden.ne'
  have herror : K*(rho*η) ≤ ε := by nlinarith only [hid,hη.le]
  refine ⟨η,hη,?_⟩
  intro x hlo hhi
  obtain ⟨i,hi⟩ := policyHeightAssociation_extended k curve coefficient p ev h hguard hchain
    x (rho*η) (mul_nonneg hrho hη.le) hlo hhi
  refine ⟨i,hi.trans ?_⟩
  exact add_le_add_left herror _

/-- Every checked degree-eight round, every policy, and every actual height
in the enlarged interval are covered. -/
theorem certificate8_extended_heights (round : Round) (hr : round ∈ heightCheckedRounds8)
    (i : Fin policies8.size) (x κ : ℝ) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x)
    (hhi : x ≤ (terminalParameters 8 round.interpolation.values policies8[i.val]!).top) :
    ∃ j : Fin policies8[i.val]!.pieces.size,
      let p := policies8[i.val]!
      let params := terminalParameters 8 round.interpolation.values p
      pieceResidualReal 8 p coefficient8.values p.pieces[j.val]!
        params.base params.slope params.scale x ≤
        max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
          (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ)+
          boundaryErrorConstant params*κ :=
  policyHeightAssociation_extended 8 round.interpolation.values coefficient8.values
    policies8[i.val]! round.entries[i.val]!.evaluation
    ((heightCheckedRounds8_association round hr).2 i) (all_policies8_guards i)
    (policies8_piece_chains i) x κ hκ hlo hhi

/-- Every checked degree-nine round has the same enlarged-height guarantee. -/
theorem certificate9_extended_heights (round : Round) (hr : round ∈ heightCheckedRounds9)
    (i : Fin policies9.size) (x κ : ℝ) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ x)
    (hhi : x ≤ (terminalParameters 9 round.interpolation.values policies9[i.val]!).top) :
    ∃ j : Fin policies9[i.val]!.pieces.size,
      let p := policies9[i.val]!
      let params := terminalParameters 9 round.interpolation.values p
      pieceResidualReal 9 p coefficient9.values p.pieces[j.val]!
        params.base params.slope params.scale x ≤
        max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
          (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ)+
          boundaryErrorConstant params*κ :=
  policyHeightAssociation_extended 9 round.interpolation.values coefficient9.values
    policies9[i.val]! round.entries[i.val]!.evaluation
    ((heightCheckedRounds9_association round hr).2 i) (all_policies9_guards i)
    (policies9_piece_chains i) x κ hκ hlo hhi

#print axioms policyHeightAssociation_extended_epsilon
#print axioms certificate8_extended_heights
#print axioms certificate9_extended_heights
end Waring.Certificate
