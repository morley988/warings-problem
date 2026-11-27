import Waring.CertificateCore
namespace Waring.Certificate

/-- Acceptance records exact equality with the rational evaluator and the unique
upward grid enclosure. This statement has no analytic premise. -/
theorem checkEntry_sound (k : Nat) (curve coefficient : Curve) (policy : Policy)
    (entry : Entry) (h : checkEntry k curve coefficient policy entry = true) :
    evaluate k curve coefficient policy = some entry.evaluation ∧
    entry.evaluation.raw ≤ entry.rounded ∧
    entry.rounded - 1/1000000000000 < entry.evaluation.raw ∧
    (entry.rounded*1000000000000).den = 1 := by
  unfold checkEntry at h
  cases heval : evaluate k curve coefficient policy with
  | none => simp [heval] at h
  | some result =>
    simp only [heval, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : result = entry.evaluation := h.1
    subst result
    refine ⟨rfl, ?_⟩
    simpa only [checkRounding, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      and_assoc] using h.2

/-- Every accepted interpolation selects a genuine chord with endpoints within
the supplied table. Its weights are therefore nonnegative and sum to one. -/
theorem checkInterpolation_sound (raw : Curve) (c : InterpolatedCurve)
    (h : checkInterpolation raw c = true) :
    raw.size = c.values.size ∧ raw.size = c.witnesses.size ∧
    ∀ i, i < raw.size → checkInterpolationAt raw c i = true := by
  simpa only [checkInterpolation, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc] using h

theorem checkedInterpolation_chord (raw : Curve) (c : InterpolatedCurve)
    (h : checkInterpolation raw c = true) (i : Nat) (hi : i < raw.size) :
    let a := c.witnesses[i]!.1
    let b := c.witnesses[i]!.2
    a ≤ i ∧ i ≤ b ∧ b < raw.size ∧
    c.values[i]! = (if a == b then raw[a]!
      else (q (b-i)*raw[a]!+q (i-a)*raw[b]!)/q (b-a)) := by
  have hc := (checkInterpolation_sound raw c h).2.2 i hi
  simpa only [checkInterpolationAt, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] using hc

/-- An accepted round links to its preceding snapshot and certifies every policy
against that same interpolated snapshot, as well as the exact output update. -/
theorem checkRound_sound (k : Nat) (policies : Array Policy) (coefficient previous : Curve)
    (round : Round) (h : checkRound k policies coefficient previous round = true) :
    round.inputs = previous ∧
    checkInterpolation round.inputs round.interpolation = true ∧
    policies.size = round.entries.size ∧
    (∀ i, i < policies.size → checkRoundEntry k policies coefficient round i = true) ∧
    updatedCurve policies round = round.outputs := by
  simpa only [checkRound, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc] using h

/-- Extraction of one policy's exact evaluator result and rounding bound from an
accepted round. The bound is tied to the computed raw value, not a free literal. -/
theorem checkedRound_entry (k : Nat) (policies : Array Policy) (coefficient previous : Curve)
    (round : Round) (h : checkRound k policies coefficient previous round = true)
    (i : Nat) (hi : i < policies.size) :
    evaluate k round.interpolation.values coefficient policies[i]! = some round.entries[i]!.evaluation ∧
    round.entries[i]!.evaluation.raw ≤ round.entries[i]!.rounded := by
  have hc := (checkRound_sound k policies coefficient previous round h).2.2.2.1 i hi
  simp only [checkRoundEntry, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hs := checkEntry_sound k round.interpolation.values coefficient policies[i]! round.entries[i]! hc.2
  exact ⟨hs.1, hs.2.1⟩

#print axioms checkEntry_sound
#print axioms checkRound_sound
end Waring.Certificate
