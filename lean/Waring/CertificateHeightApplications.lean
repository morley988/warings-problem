import Waring.CertificateHeightChecked
import Mathlib.Tactic.FinCases

/-!
# All-height consequences for the frozen certificates

Each listed round is tied to its stored endpoints by kernel-checked rational
identities. The resulting inequalities quantify over all real points of every
actual policy piece. They certify the height optimization algebra, not the
separate analytic estimates assigned to the resources.
-/

noncomputable section
namespace Waring.Certificate

theorem policyHeightAssociation_all_heights (k : Nat) (curve coefficient : Curve)
    (p : Policy) (ev : Evaluation) (h : PolicyHeightAssociation k curve coefficient p ev)
    (hguard : PolicyAnalyticGuards k p) (i : Fin p.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (p.pieces[i.val]!.lo : ℝ) (p.pieces[i.val]!.hi : ℝ)) :
    let params := terminalParameters k curve p
    pieceResidualReal k p coefficient p.pieces[i.val]! params.base params.slope params.scale
      (1+t*((params.top : ℝ)-1)) ≤
        max (ev.pieces[i.val]!.endpoints[0]!.exponent : ℝ)
          (ev.pieces[i.val]!.endpoints[1]!.exponent : ℝ) := by
  have hp : p.pieces[i.val]! ∈ p.pieces.toList := by
    rw [getElem!_pos p.pieces i.val i.isLt]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)
  exact pieceHeightAssociation_all_heights k p coefficient p.pieces[i.val]!
    (terminalParameters k curve p) ev.pieces[i.val]! (h.2.2.2 i)
    (policyGuards_weights_nonneg k p hguard _ hp) h.2.1 h.1 t ht

theorem roundHeightAssociation_all_heights (k : Nat) (policies : Array Policy)
    (coefficient : Curve) (round : Round) (h : RoundHeightAssociation k policies coefficient round)
    (hguards : ∀ i : Fin policies.size, PolicyAnalyticGuards k policies[i.val]!)
    (i : Fin policies.size) (j : Fin policies[i.val]!.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (policies[i.val]!.pieces[j.val]!.lo : ℝ)
      (policies[i.val]!.pieces[j.val]!.hi : ℝ)) :
    let p := policies[i.val]!
    let params := terminalParameters k round.interpolation.values p
    pieceResidualReal k p coefficient p.pieces[j.val]! params.base params.slope params.scale
      (1+t*((params.top : ℝ)-1)) ≤
        max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
          (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ) :=
  policyHeightAssociation_all_heights k round.interpolation.values coefficient policies[i.val]!
    round.entries[i.val]!.evaluation (h.2 i) (hguards i) j t ht

theorem all_policies8_guards (i : Fin policies8.size) :
    PolicyAnalyticGuards 8 policies8[i.val]! := by
  change Fin 4 at i
  fin_cases i
  · exact policy8_0_guards
  · exact policy8_1_guards
  · exact policy8_2_guards
  · exact policy8_3_guards

theorem all_policies9_guards (i : Fin policies9.size) :
    PolicyAnalyticGuards 9 policies9[i.val]! := by
  change Fin 4 at i
  fin_cases i
  · exact policy9_0_guards
  · exact policy9_1_guards
  · exact policy9_2_guards
  · exact policy9_3_guards

def heightCheckedRounds8 : List Round :=
  [round8_01, round8_02, round8_03, round8_04, round8_05, round8_06,
   round8_07, round8_08, round8_09, round8_10, round8_11, round8_12]

def heightCheckedRounds9 : List Round :=
  [round9_01, round9_02, round9_03, round9_04, round9_05, round9_06]

theorem heightCheckedRounds8_association :
    ∀ round ∈ heightCheckedRounds8, RoundHeightAssociation 8 policies8 coefficient8.values round := by
  simp only [heightCheckedRounds8, List.forall_mem_cons]
  exact ⟨round8_01_height_association, round8_02_height_association,
    round8_03_height_association, round8_04_height_association,
    round8_05_height_association, round8_06_height_association,
    round8_07_height_association, round8_08_height_association,
    round8_09_height_association, round8_10_height_association,
    round8_11_height_association, round8_12_height_association, by simp⟩

theorem heightCheckedRounds9_association :
    ∀ round ∈ heightCheckedRounds9, RoundHeightAssociation 9 policies9 coefficient9.values round := by
  simp only [heightCheckedRounds9, List.forall_mem_cons]
  exact ⟨round9_01_height_association, round9_02_height_association,
    round9_03_height_association, round9_04_height_association,
    round9_05_height_association, round9_06_height_association, by simp⟩

theorem certificate8_all_real_heights (round : Round) (hr : round ∈ heightCheckedRounds8)
    (i : Fin policies8.size) (j : Fin policies8[i.val]!.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (policies8[i.val]!.pieces[j.val]!.lo : ℝ)
      (policies8[i.val]!.pieces[j.val]!.hi : ℝ)) :
    let p := policies8[i.val]!
    let params := terminalParameters 8 round.interpolation.values p
    pieceResidualReal 8 p coefficient8.values p.pieces[j.val]! params.base params.slope params.scale
      (1+t*((params.top : ℝ)-1)) ≤
        max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
          (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ) :=
  roundHeightAssociation_all_heights 8 policies8 coefficient8.values round
    (heightCheckedRounds8_association round hr) all_policies8_guards i j t ht

theorem certificate9_all_real_heights (round : Round) (hr : round ∈ heightCheckedRounds9)
    (i : Fin policies9.size) (j : Fin policies9[i.val]!.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (policies9[i.val]!.pieces[j.val]!.lo : ℝ)
      (policies9[i.val]!.pieces[j.val]!.hi : ℝ)) :
    let p := policies9[i.val]!
    let params := terminalParameters 9 round.interpolation.values p
    pieceResidualReal 9 p coefficient9.values p.pieces[j.val]! params.base params.slope params.scale
      (1+t*((params.top : ℝ)-1)) ≤
        max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
          (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ) :=
  roundHeightAssociation_all_heights 9 policies9 coefficient9.values round
    (heightCheckedRounds9_association round hr) all_policies9_guards i j t ht

#print axioms certificate8_all_real_heights
#print axioms certificate9_all_real_heights
end Waring.Certificate
