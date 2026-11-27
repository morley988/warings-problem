import Waring.EndgameCompletionPolicySemanticsParameters

/-! # Kernel-checked analytic metadata of the original frozen policies

These checks establish every order and array lookup used by the analytic
recurrence. They do not infer an analytic estimate from evaluator acceptance.
All curves, policies and stored exponents remain the original certificate data.
-/

noncomputable section
namespace Waring.Certificate

def PolicyShapeAssociation (k : ℕ) (p : Policy) : Prop :=
  4≤k ∧ 2≤p.halfOrder ∧ 1≤p.phi.size ∧ p.phi.size+2≤k ∧
  p.path.size=p.phi.size ∧ p.path[0]! =p.halfOrder-1 ∧
  (∀ i : Fin p.phi.size,0<p.path[i.val]!) ∧
  (∀ i : Fin (p.phi.size-1),p.path[i.val+1]!<2*p.path[i.val]!) ∧
  0<terminalFullOrder p ∧
  0≤terminalWeightQ p ∧ terminalWeightQ p≤1 ∧
  0≤1-2*(1-terminalWeightQ p) ∧
  terminalWeightQ p*q (terminalFullOrder p)=q (2*terminalHalfOrder p) ∧
  (p.auxiliaryOrder.isSome=true → p.phi.size=k-2)

instance (k : ℕ) (p : Policy) : Decidable (PolicyShapeAssociation k p) := by
  unfold PolicyShapeAssociation
  infer_instance

def PolicyMomentAssociation (k : ℕ) (curve coefficient : Curve)
    (p : Policy) (ev : Evaluation) : Prop :=
  MomentAvailable curve (2*(p.halfOrder-1)) ∧
  MomentAvailable curve (2*terminalHalfOrder p) ∧
  MomentAvailable curve (terminalFullOrder p) ∧
  (∀ i : Fin p.phi.size,MomentAvailable curve (2*p.path[i.val]!)) ∧
  (∀ i : Fin (p.phi.size-1),
    MomentAvailable curve (2*(2*p.path[i.val]!-p.path[i.val+1]!))) ∧
  (∀ i : Fin p.pieces.size,∀ r : Fin p.pieces[i.val]!.resources.size,
    MomentAvailable coefficient p.pieces[i.val]!.resources[r.val]!.order) ∧
  ev.major=terminalMajorFormula k curve p

instance (k : ℕ) (curve coefficient : Curve) (p : Policy) (ev : Evaluation) :
    Decidable (PolicyMomentAssociation k curve coefficient p ev) := by
  unfold PolicyMomentAssociation
  infer_instance

def RoundMomentAssociation (k : ℕ) (policies : Array Policy)
    (coefficient : Curve) (round : Round) : Prop :=
  ∀ i : Fin policies.size,PolicyMomentAssociation k round.interpolation.values coefficient
    policies[i.val]! round.entries[i.val]!.evaluation

instance (k : ℕ) (policies : Array Policy) (coefficient : Curve) (round : Round) :
    Decidable (RoundMomentAssociation k policies coefficient round) := by
  unfold RoundMomentAssociation
  infer_instance

theorem all_policies8_shape : ∀ i : Fin policies8.size,
    PolicyShapeAssociation 8 policies8[i.val]! := by decide +kernel

theorem all_policies9_shape : ∀ i : Fin policies9.size,
    PolicyShapeAssociation 9 policies9[i.val]! := by decide +kernel

theorem round8_01_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_01 := by decide +kernel

theorem round8_02_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_02 := by decide +kernel

theorem round8_03_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_03 := by decide +kernel

theorem round8_04_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_04 := by decide +kernel

theorem round8_05_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_05 := by decide +kernel

theorem round8_06_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_06 := by decide +kernel

theorem round8_07_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_07 := by decide +kernel

theorem round8_08_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_08 := by decide +kernel

theorem round8_09_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_09 := by decide +kernel

theorem round8_10_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_10 := by decide +kernel

theorem round8_11_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_11 := by decide +kernel

theorem round8_12_moment_association :
    RoundMomentAssociation 8 policies8 coefficient8.values round8_12 := by decide +kernel

theorem round9_01_moment_association :
    RoundMomentAssociation 9 policies9 coefficient9.values round9_01 := by decide +kernel

theorem round9_02_moment_association :
    RoundMomentAssociation 9 policies9 coefficient9.values round9_02 := by decide +kernel

theorem round9_03_moment_association :
    RoundMomentAssociation 9 policies9 coefficient9.values round9_03 := by decide +kernel

theorem round9_04_moment_association :
    RoundMomentAssociation 9 policies9 coefficient9.values round9_04 := by decide +kernel

theorem round9_05_moment_association :
    RoundMomentAssociation 9 policies9 coefficient9.values round9_05 := by decide +kernel

theorem round9_06_moment_association :
    RoundMomentAssociation 9 policies9 coefficient9.values round9_06 := by decide +kernel

theorem heightCheckedRounds8_moments :
    ∀ round ∈ heightCheckedRounds8,RoundMomentAssociation 8 policies8 coefficient8.values round := by
  simp only [heightCheckedRounds8,List.forall_mem_cons]
  exact ⟨round8_01_moment_association,round8_02_moment_association,
    round8_03_moment_association,round8_04_moment_association,
    round8_05_moment_association,round8_06_moment_association,
    round8_07_moment_association,round8_08_moment_association,
    round8_09_moment_association,round8_10_moment_association,
    round8_11_moment_association,round8_12_moment_association,by simp⟩

theorem heightCheckedRounds9_moments :
    ∀ round ∈ heightCheckedRounds9,RoundMomentAssociation 9 policies9 coefficient9.values round := by
  simp only [heightCheckedRounds9,List.forall_mem_cons]
  exact ⟨round9_01_moment_association,round9_02_moment_association,
    round9_03_moment_association,round9_04_moment_association,
    round9_05_moment_association,round9_06_moment_association,by simp⟩

#print axioms all_policies8_shape
#print axioms all_policies9_shape
#print axioms heightCheckedRounds8_moments
#print axioms heightCheckedRounds9_moments
end Waring.Certificate
